import Mathlib
import OAI.Probability.Perceptron.Variational.EnrichedUniformBounds
import OAI.Probability.Perceptron.Variational.IndexedAncestry

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section
variable {I : Type} [Fintype I] {S : Type} [MeasurableSpace S]

omit [MeasurableSpace S] in
lemma indexedGaussianRow_mask (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (i : ℕ) (x : S×IndexedLeaf n) :
    maskedGaussianCoefficient (indexedGaussianRow n B V) (indexedGaussianRowLength (I := I) n) i x =
      indexedGaussianRow n B V i x := by
  unfold maskedGaussianCoefficient
  split_ifs with hi
  · rfl
  · exact (finiteGaussianRow_tail _ _ i (Nat.le_of_not_gt hi)).symm

lemma indexedGaussianRowKey_eq (n : ℕ) (l m : IndexedLeaf n) (a b : Fin (n+1)×I) :
    indexedGaussianRowKey n m b = indexedGaussianRowKey n l a ↔
      b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n m l := by
  rw [indexedGaussianRowKey,indexedGaussianRowKey,countableCoordinate_injective.eq_iff,
    Prod.mk.injEq,indexedLeafSharedVertex_eq_iff_pair]
  constructor
  · rintro ⟨⟨he,hc⟩,hi⟩
    exact ⟨he,hi,he ▸ hc⟩
  · rintro ⟨he,hi,hc⟩
    exact ⟨⟨he,he.symm ▸ hc⟩,hi⟩

omit [MeasurableSpace S] in
lemma indexedGaussianRow_cross_value (n : ℕ) (B : Fin (n+1) → I → ℝ)
    (V : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) (a : Fin (n+1)×I) :
    indexedGaussianRow n B V (indexedGaussianRowKey n x.2 a) y =
      if a.1 ≤ indexedCommonDepth n y.2 x.2 then B a.1 a.2*V y.1 a.2 else 0 := by
  classical
  unfold indexedGaussianRow finiteGaussianRow
  simp_rw [indexedGaussianRowKey_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hd : ¬ (b.1=a.1 ∧ b.2=a.2 ∧ a.1 ≤ indexedCommonDepth n y.2 x.2) := by
      rintro ⟨h1,h2,_⟩
      exact hba (Prod.ext h1 h2)
    simp [hd]
  · simp

omit [MeasurableSpace S] in
lemma indexedGaussianRow_covariance (n : ℕ) (B C : Fin (n+1) → I → ℝ)
    (V W : S → EuclideanSpace ℝ I) (x y : S×IndexedLeaf n) :
    countableGaussianCovariance (indexedGaussianRow n B V) (indexedGaussianRow n C W)
      (indexedGaussianRowLength (I := I) n) x y =
      ∑ i : I, (∑ j : Fin (n+1), if j ≤ indexedCommonDepth n y.2 x.2 then C j i*B j i else 0)*W x.1 i*V y.1 i := by
  classical
  unfold countableGaussianCovariance gaussianPrefixCovariance
  simp_rw [indexedGaussianRow_mask]
  change (∑ i : Fin (finiteGaussianRowLength (indexedGaussianRowKey (I := I) n x.2)),
    finiteGaussianRow (indexedGaussianRowKey n x.2) (fun p => C p.1 p.2*W x.1 p.2) i.val*
      indexedGaussianRow n B V i.val y) = _
  rw [finiteGaussianRow_sum (indexedGaussianRowKey_injective n x.2) _
    (fun i z => z*indexedGaussianRow n B V i y) (fun i => zero_mul _)]
  simp_rw [indexedGaussianRow_cross_value]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

end

lemma finite_profile_prefix {k : ℕ} (q : Fin (k+1) → ℝ) (a : Fin (k+1)) :
    q 0 + ∑ j : Fin k, (if j.succ ≤ a then q j.succ-q j.castSucc else 0) = q a := by
  have he (j : Fin k) : (if j.succ ≤ a then q j.succ-q j.castSucc else 0) =
      q (min j.succ a)-q (min j.castSucc a) := by
    by_cases hj : j.succ ≤ a
    · rw [ite_eq_left hj,min_eq_left hj,min_eq_left ((Fin.castSucc_le_succ j).trans hj)]
    · have hc : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val,Fin.val_castSucc,Fin.val_succ] at *
        omega
      rw [ite_eq_right hj,min_eq_right (le_of_not_ge hj),min_eq_right hc,sub_self]
  simp_rw [he]
  simpa only [min_eq_left (Fin.zero_le a),min_eq_right (Fin.le_last a)] using
    finite_profile_telescope (fun l => q (min l a))

lemma profileGaussian_coefficient_prefix {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (a : Fin (k+1)) (i : I) :
    (∑ l : Fin (k+1), if l ≤ a then
      hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2 else 0) = q a i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Fin.zero_le,ite_true,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (Fin.castSucc_le_succ j)))
  simp_rw [he]
  exact finite_profile_prefix (fun l => q l i) a

lemma profileGaussianRow_covariance {I S : Type} [Fintype I] [MeasurableSpace S]
    {k : ℕ} (q : Fin (k+1) → I → ℝ) (h0 : ∀ i, 0 ≤ q 0 i)
    (hq : ∀ i, Monotone (fun l => q l i)) (V W : S → EuclideanSpace ℝ I)
    (x y : S×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) V)
      (indexedGaussianRow k (hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q)) W)
      (indexedGaussianRowLength (I := I) k) x y =
      ∑ i : I, q (indexedCommonDepth k y.2 x.2) i*W x.1 i*V y.1 i := by
  rw [indexedGaussianRow_covariance]
  simp_rw [← sq,profileGaussian_coefficient_prefix q h0 hq]

lemma enrichedFeature_profile_cross {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (l : Fin (k+1)) (a b : ℝ) (c e : Fin N → ℝ) (x y : NormalizedSpin N) :
    (∑ i : EnrichedIndex N N p, enrichedCoordinateLevel p d h l i*
      enrichedFeature N N p a c x i*enrichedFeature N N p b e y i) =
      2*h l*a*b*spinOverlap x y+
        ∑ j, (((l.val:ℝ)/(k+1:ℕ))^(d j))*c j*e j*spinOverlap x y^(p j) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  have hlin : (∑ i : Fin N, enrichedCoordinateLevel p d h l (.inl i)*
      enrichedFeature N N p a c x (.inl i)*enrichedFeature N N p b e y (.inl i)) =
      2*h l*a*b*spinOverlap x y := by
    change (∑ i : Fin N, 2*h l*(a*x.val i)*(b*y.val i)) =
      2*h l*a*b*(∑ i : Fin N, y.val i*x.val i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hlin]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← spinTensorFeature_inner N (p j) x y]
  change (∑ t : SpinTensorIndex N (p j), (((l.val:ℝ)/(k+1:ℕ))^(d j))*
      (c j*spinTensorFeature N (p j) x t)*(e j*spinTensorFeature N (p j) y t)) =
      (((l.val:ℝ)/(k+1:ℕ))^(d j))*c j*e j*
        (∑ t : SpinTensorIndex N (p j), spinTensorFeature N (p j) y t*spinTensorFeature N (p j) x t)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma sourceGaussianRow_covariance {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin N → ℝ)
    (x y : NormalizedSpin N×IndexedLeaf k) :
    countableGaussianCovariance (sourceGaussianRow p d h u) (sourceGaussianRow p d h u)
      (indexedGaussianRowLength (I := EnrichedIndex N N p) k) x y =
      2*(N:ℝ)*h (indexedCommonDepth k y.2 x.2)*spinOverlap x.1 y.1+
        ∑ j, perturbationAmplitude N u j^2*
          (((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ))^(d j)*spinOverlap x.1 y.1^(p j) := by
  unfold sourceGaussianRow
  rw [profileGaussianRow_covariance _ (enrichedCoordinateLevel_nonneg p d hh0 0)
    (enrichedCoordinateLevel_monotone p d hh)]
  unfold sourceEnrichedFeature
  rw [enrichedFeature_profile_cross]
  have hl : 2*h (indexedCommonDepth k y.2 x.2)*Real.sqrt (N:ℝ)*Real.sqrt (N:ℝ)*spinOverlap x.1 y.1 =
      2*(N:ℝ)*h (indexedCommonDepth k y.2 x.2)*spinOverlap x.1 y.1 := by
    calc
      _ = 2*h (indexedCommonDepth k y.2 x.2)*(Real.sqrt (N:ℝ))^2*spinOverlap x.1 y.1 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring
  rw [hl]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def sourceGaussianTestFeature (N : ℕ) (p : Fin N → ℕ) (j : Fin N) :
    NormalizedSpin N → EnrichedMark N N p := enrichedFeature N N p 0 (Pi.single j 1)

def sourceGaussianTestRow {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (j : Fin N) :
    ℕ → NormalizedSpin N×IndexedLeaf k → ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k
    (profileGaussianRoot (enrichedCoordinateLevel p d h))
    (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceGaussianTestFeature N p j)

lemma sourceGaussianRow_test_covariance {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin N → ℝ) (j : Fin N)
    (x y : NormalizedSpin N×IndexedLeaf k) :
    countableGaussianCovariance (sourceGaussianRow p d h u) (sourceGaussianTestRow p d h j)
      (indexedGaussianRowLength (I := EnrichedIndex N N p) k) x y =
      perturbationAmplitude N u j*
        (((indexedCommonDepth k y.2 x.2).val:ℝ)/(k+1:ℕ))^(d j)*spinOverlap x.1 y.1^(p j) := by
  unfold sourceGaussianRow sourceGaussianTestRow
  rw [profileGaussianRow_covariance _ (enrichedCoordinateLevel_nonneg p d hh0 0)
    (enrichedCoordinateLevel_monotone p d hh)]
  unfold sourceEnrichedFeature sourceGaussianTestFeature
  rw [enrichedFeature_profile_cross]
  simp only [mul_zero,zero_mul,zero_add]
  rw [Finset.sum_eq_single j]
  · simp only [Pi.single_eq_same,mul_one]
    ring
  · intro i hi hij
    simp [Pi.single_eq_of_ne hij]
  · simp

end SphericalPerceptronFreeEnergy

end

end OAI
