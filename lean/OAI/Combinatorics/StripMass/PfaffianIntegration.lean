import Mathlib
import OAI.Combinatorics.StripMass.PairCoordinates

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set
lemma integral_pair_single_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (f : Fin m → α × α → ℂ) (g : α → ℂ) :
    (∫ x : Fin (m*2+1) → α, (∏ i : Fin m,
      f i (x (pairLeft i).castSucc, x (pairRight i).castSucc)) * g (x (Fin.last (m*2)))
      ∂Measure.pi (fun _ => μ)) = (∏ i, ∫ rs, f i rs ∂μ.prod μ) * ∫ t, g t ∂μ := by
  rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m*2+1) => μ)
    (Fin.last (m*2))).symm).integral_comp']
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last, Fin.snoc_castSucc, Fin.snoc_last, cast_eq]
  simp_rw [mul_comm _ (g _)]
  rw [integral_prod_mul (μ := μ) (ν := Measure.pi (fun _ : Fin (m*2) => μ)) g
    (fun x : Fin (m*2) → α => ∏ i, f i (x (pairLeft i), x (pairRight i))),
    integral_pair_product, mul_comm]

lemma integrable_pair_single_product {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) {f : Fin m → α × α → ℂ} {g : α → ℂ}
    (hf : ∀ i, Integrable (f i) (μ.prod μ)) (hg : Integrable g μ) :
    Integrable (fun x : Fin (m*2+1) → α => (∏ i : Fin m,
      f i (x (pairLeft i).castSucc, x (pairRight i).castSucc)) * g (x (Fin.last (m*2))))
      (Measure.pi (fun _ => μ)) := by
  apply (((measurePreserving_piFinSuccAbove (fun _ : Fin (m*2+1) => μ)
    (Fin.last (m*2))).symm).integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m*2+1) => α)
        (Fin.last (m*2))).symm.measurableEmbedding).mp
  simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last,
    Fin.snoc_castSucc, Fin.snoc_last, cast_eq]
  simp_rw [mul_comm _ (g _)]
  exact hg.mul_prod (integrable_pair_product μ m hf)

def singleMoment {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    (φ : Fin n → α → ℂ) (g : α → ℂ) : Fin n → ℂ :=
  fun i => ∫ t, φ i t * g t ∂μ

lemma product_double_singleIntegrand {α : Type*} {m : ℕ} (φ : Fin (m*2+1) → α → ℂ)
    (k : α → α → ℂ) (g : α → ℂ) (σ : Equiv.Perm (Fin (m*2+1))) (x : Fin (m*2+1) → α) :
    (∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc)
      (x (pairLeft i).castSucc, x (pairRight i).castSucc)) *
        (φ (σ (Fin.last (m*2))) (x (Fin.last (m*2))) * g (x (Fin.last (m*2)))) =
      (∏ i : Fin (m*2+1), φ (σ i) (x i)) *
        oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x) := by
  unfold doubleIntegrand oddPairEntries
  rw [Fin.prod_univ_castSucc, ← prod_pairs (fun i => φ (σ i.castSucc) (x i.castSucc))]
  simp only [Finset.prod_mul_distrib, Function.comp_apply]
  ring

lemma determinant_times_oddPairs {α : Type*} {m : ℕ} (φ : Fin (m*2+1) → α → ℂ)
    (k : α → α → ℂ) (g : α → ℂ) (x : Fin (m*2+1) → α) :
    (evaluationMatrix φ x).det * oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x) =
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        ((∏ i : Fin m, doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc)
          (x (pairLeft i).castSucc, x (pairRight i).castSucc)) *
        (φ (σ (Fin.last (m*2))) (x (Fin.last (m*2))) * g (x (Fin.last (m*2))))) := by
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [product_double_singleIntegrand]
  simp only [evaluationMatrix, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  ring

lemma integrable_determinant_times_oddPairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    Integrable (fun x => (evaluationMatrix φ x).det *
      oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)) (Measure.pi (fun _ => μ)) := by
  simp only [determinant_times_oddPairs]
  exact integrable_finsetSum _ (fun σ _ =>
    (integrable_pair_single_product μ m (fun i => hi _ _) (hs _)).const_mul _)

lemma integral_determinant_times_oddPairs {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {m : ℕ} (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    (∫ x, (evaluationMatrix φ x).det * oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)
      ∂Measure.pi (fun _ => μ)) =
      ∑ σ : Equiv.Perm (Fin (m*2+1)), (Equiv.Perm.sign σ : ℂ) *
        oddPairEntries (fun i j => doubleMomentMatrix μ φ k (σ i) (σ j))
          (singleMoment μ φ g ∘ σ) := by
  simp only [determinant_times_oddPairs]
  rw [integral_finsetSum _ (fun σ _ =>
    (integrable_pair_single_product μ m (fun i => hi _ _) (hs _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [integral_const_mul]
  congr 1
  exact integral_pair_single_product μ m
    (fun i => doubleIntegrand φ k (σ (pairLeft i).castSucc) (σ (pairRight i).castSucc))
    (fun t => φ (σ (Fin.last (m*2))) t * g t)

 

theorem deBruijn_odd {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (m : ℕ) (φ : Fin (m*2+1) → α → ℂ) (k : α → α → ℂ) (g : α → ℂ)
    (hk : ∀ r s, k s r = -k r s)
    (hi : ∀ i j, Integrable (doubleIntegrand φ k i j) (μ.prod μ))
    (hs : ∀ i, Integrable (fun t => φ i t * g t) μ) :
    (∫ x, (evaluationMatrix φ x).det *
      pfaffian (m*2+2) (border (fun i j => k (x i) (x j)) (g ∘ x))
      ∂Measure.pi (fun _ => μ)) =
        (Nat.factorial (m*2+1) : ℂ) * pfaffian (m*2+2)
          (border (doubleMomentMatrix μ φ k) (singleMoment μ φ g)) := by
  let F : (Fin (m*2+1) → α) → ℂ := fun x => (evaluationMatrix φ x).det
  let G : (Fin (m*2+1) → α) → ℂ := fun x => oddPairEntries (fun i j => k (x i) (x j)) (g ∘ x)
  have hF (σ : Equiv.Perm (Fin (m*2+1))) (x : Fin (m*2+1) → α) :
      F (x ∘ σ) = (Equiv.Perm.sign σ : ℂ) * F x := evaluationMatrix_det_perm φ σ x
  have hI := integrable_determinant_times_oddPairs μ φ k g hi hs
  have hII (σ : Equiv.Perm (Fin (m*2+1))) :
      Integrable (fun x => F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)))
        (Measure.pi (fun _ => μ)) := by
    have h := (integrable_alternating_times_perm μ F G hF hI σ).const_mul (Equiv.Perm.sign σ : ℂ)
    convert h using 1
    ext x
    ring
  have hpoint (x : Fin (m*2+1) → α) :
      F x * pfaffian (m*2+2) (border (fun i j => k (x i) (x j)) (g ∘ x)) =
        ((1/2:ℂ)^m / m.factorial) *
          ∑ σ : Equiv.Perm (Fin (m*2+1)), F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) := by
    rw [pfaffian_border_permutation_expansion m _ (fun i j => hk _ _)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    dsimp [F, G, Function.comp_def]
    ring
  change (∫ x, F x * pfaffian (m*2+2) _ ∂Measure.pi (fun _ => μ)) = _
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finsetSum _ (fun σ _ => hII σ)]
  have he (σ : Equiv.Perm (Fin (m*2+1))) :
      (∫ x, F x * ((Equiv.Perm.sign σ : ℂ) * G (x ∘ σ)) ∂Measure.pi (fun _ => μ)) =
        ∫ x, F x * G x ∂Measure.pi (fun _ => μ) := by
    calc
      _ = (Equiv.Perm.sign σ : ℂ) * ∫ x, F x * G (x ∘ σ) ∂Measure.pi (fun _ => μ) := by
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ = _ := by
        rw [integral_alternating_times_perm μ F G hF, ← mul_assoc]
        have hs : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
          have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
            congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
          exact_mod_cast hs
        rw [hs, one_mul]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
    pfaffian_border_permutation_expansion m _ (doubleMomentMatrix_skew μ φ k hk),
    ← integral_determinant_times_oddPairs μ φ k g hi hs]
  dsimp [F,G]
  ring

end
end StripPfaffian

 

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

lemma laguerreDomain_subset_positive (n : ℕ) :
    laguerreDomain n ⊆ univ.pi (fun _ : Fin n => Ioi (0 : ℝ)) :=
  fun _ hr i _ => hr.2 i

lemma positive_product_restrict_chamber (n : ℕ) :
    (Measure.pi (fun _ : Fin n => μ₊)).restrict (laguerreDomain n) =
      volume.restrict (laguerreDomain n) := by
  rw [← Measure.restrict_pi_pi, ← volume_pi,
    Measure.restrict_restrict (isOpen_laguerreDomain n).measurableSet,
    inter_eq_left.mpr (laguerreDomain_subset_positive n)]

lemma ae_positive_product (n : ℕ) :
    ∀ᵐ x : Fin n → ℝ ∂Measure.pi (fun _ => μ₊), ∀ i, 0 < x i := by
  rw [← Measure.restrict_pi_pi, ← volume_pi]
  exact (ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)).mono
    fun _ hx i => hx i (mem_univ i)

lemma sum_ordered_indicator {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (∑ σ : Equiv.Perm (Fin n), (laguerreDomain n).indicator F (x ∘ σ)) = F x := by
  classical
  by_cases hi : Function.Injective x
  · have hs : x ∘ Tuple.sort x ∈ laguerreDomain n :=
      ⟨(Tuple.monotone_sort x).strictMono_of_injective (hi.comp (Tuple.sort x).injective),
        fun i => hx _⟩
    rw [Finset.sum_eq_single (Tuple.sort x)]
    · rw [indicator_of_mem hs, hperm]
    · intro σ hσ hne
      apply indicator_of_notMem
      intro hσs
      apply hne
      apply Equiv.ext
      intro i
      exact hi (congrFun (Tuple.unique_monotone hσs.1.monotone (Tuple.monotone_sort x)) i)
    · simp
  · rw [hzero x hi]
    apply Finset.sum_eq_zero
    intro σ hσ
    by_cases hm : x ∘ σ ∈ laguerreDomain n
    · rw [indicator_of_mem hm, hperm, hzero x hi]
    · exact indicator_of_notMem hm _

 

lemma integral_symmetric_ordered {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (hperm : ∀ σ : Equiv.Perm (Fin n), ∀ x, F (x ∘ σ) = F x)
    (hzero : ∀ x, ¬Function.Injective x → F x = 0)
    (hint : IntegrableOn F (laguerreDomain n)) :
    (∫ x, F x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * ∫ x in laguerreDomain n, F x := by
  classical
  let G := (laguerreDomain n).indicator F
  have hi : Integrable G (Measure.pi (fun _ : Fin n => μ₊)) := by
    rw [integrable_indicator_iff (isOpen_laguerreDomain n).measurableSet]
    simpa only [IntegrableOn, positive_product_restrict_chamber] using hint
  have his (σ : Equiv.Perm (Fin n)) :
      Integrable (fun x => G (x ∘ σ)) (Measure.pi (fun _ : Fin n => μ₊)) := by
    simpa only [Function.comp_def, piCongrLeft_const_apply, Equiv.symm_symm] using
      (measurePreserving_piCongrLeft (fun _ : Fin n => μ₊) σ.symm).integrable_comp_of_integrable hi
  have heq (σ : Equiv.Perm (Fin n)) :
      (∫ x, G (x ∘ σ) ∂Measure.pi (fun _ : Fin n => μ₊)) =
        ∫ x in laguerreDomain n, F x := by
    have he := (measurePreserving_piCongrLeft (fun _ : Fin n => μ₊) σ.symm).integral_comp' G
    simp only [piCongrLeft_const_apply, Equiv.symm_symm] at he
    rw [he, integral_indicator (isOpen_laguerreDomain n).measurableSet,
      positive_product_restrict_chamber]
  calc
    _ = ∫ x, ∑ σ : Equiv.Perm (Fin n), G (x ∘ σ) ∂Measure.pi (fun _ => μ₊) := by
      apply integral_congr_ae
      exact (ae_positive_product n).mono fun x hx => (sum_ordered_indicator F hperm hzero x hx).symm
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ x, G (x ∘ σ) ∂Measure.pi (fun _ => μ₊) :=
      integral_finsetSum _ (fun σ _ => his σ)
    _ = _ := by simp only [heq, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end
end CriticalStrip

namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set

lemma permMap_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Vec n) :
    permMap n σ u = u ∘ σ.symm := by
  have hu : ∑ i : Fin n, u i • standardBasis n i = u := by
    simpa only [standardBasis, Pi.basisFun_repr] using (standardBasis n).sum_repr u
  calc
    _ = ∑ i : Fin n, u i • standardBasis n (σ i) := by
      conv_lhs => rw [← hu]
      simp only [map_sum, map_smul, permMap_basis]
    _ = ∑ i : Fin n, u (σ.symm i) • standardBasis n i := by
      apply Fintype.sum_equiv σ
      intro i
      simp
    _ = _ := by simpa only [standardBasis, Pi.basisFun_repr, Function.comp_apply] using
      (standardBasis n).sum_repr (u ∘ σ.symm)

lemma pfaffian_border_perm {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (u : Vec n)
    (σ : Equiv.Perm (Fin n)) :
    pfaffian (n+1) (border (fun i j => A (σ.symm i) (σ.symm j)) (u ∘ σ.symm)) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian (n+1) (border A u) := by
  have hn' : 2*(n/2)+1 = n := by obtain ⟨k, hk⟩ := hn; omega
  have hhom : twoForm A ^ (n/2) * ExteriorAlgebra.ι ℂ u ∈
      ExteriorAlgebra.exteriorPower ℂ n (Vec n) := by
    simpa only [hn'] using SetLike.mul_mem_graded (twoForm_pow_mem A (n/2))
      (show ExteriorAlgebra.ι ℂ u ∈ ExteriorAlgebra.exteriorPower ℂ 1 (Vec n) from by
        simpa only [ExteriorAlgebra.exteriorPower, pow_one] using
          (LinearMap.mem_range_self (ExteriorAlgebra.ι ℂ) u))
  erw [pfaffian_border hn _ (fun i j => hA _ _), pfaffian_border hn A hA,
    borderLinear_eq_topCoord hn, borderLinear_eq_topCoord hn,
    ← twoForm_perm A hA σ, ← permMap_apply σ u, ← ExteriorAlgebra.map_apply_ι,
    ← map_pow, ← map_mul, topCoord_map _ _ _ hhom, permMap_det]
  ring

lemma perm_sign_mul_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
  have hs : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 :=
    congrArg Units.val (Int.units_mul_self (Equiv.Perm.sign σ))
  exact_mod_cast hs

lemma determinantPfaffian_symmetric_even {α : Type*} {n : ℕ} (hn : Even n)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) (hk : ∀ r s, k s r = -k r s)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det * pfaffian n (fun i j => k (x (σ i)) (x (σ j))) =
      (evaluationMatrix φ x).det * pfaffian n (fun i j => k (x i) (x j)) := by
  rw [evaluationMatrix_det_perm]
  have hp := pfaffian_perm n hn (fun i j => k (x i) (x j)) (fun i j => hk _ _) σ.symm
  simp only [Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  erw [hp]
  calc
    _ = ((Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)) *
      ((evaluationMatrix φ x).det * pfaffian n (fun i j => k (x i) (x j))) := by ring
    _ = _ := by rw [perm_sign_mul_self, one_mul]

lemma determinantPfaffian_symmetric_odd {α : Type*} {n : ℕ} (hn : Odd n)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) (g : α → ℂ) (hk : ∀ r s, k s r = -k r s)
    (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    (evaluationMatrix φ (x ∘ σ)).det * pfaffian (n+1)
      (border (fun i j => k (x (σ i)) (x (σ j))) (g ∘ x ∘ σ)) =
      (evaluationMatrix φ x).det * pfaffian (n+1)
        (border (fun i j => k (x i) (x j)) (g ∘ x)) := by
  rw [evaluationMatrix_det_perm]
  have hp := pfaffian_border_perm hn (fun i j => k (x i) (x j))
    (fun i j => hk _ _) (g ∘ x) σ.symm
  simp only [Equiv.symm_symm, Equiv.Perm.sign_symm] at hp
  erw [hp]
  calc
    _ = ((Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ)) *
      ((evaluationMatrix φ x).det * pfaffian (n+1)
        (border (fun i j => k (x i) (x j)) (g ∘ x))) := by ring
    _ = _ := by rw [perm_sign_mul_self, one_mul]

lemma evaluationMatrix_det_of_not_injective {α : Type*} {n : ℕ}
    (φ : Fin n → α → ℂ) {x : Fin n → α} (hx : ¬Function.Injective x) :
    (evaluationMatrix φ x).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hx
  exact Matrix.det_zero_of_column_eq hne (fun r => congrArg (φ r) hij)

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

def laguerrePhi (n : ℕ) (a : ℝ) (i : Fin n) (x : ℝ) : ℂ := laguerreWeight (a+i.val) x

lemma laguerreWeight_shift_nat (a : ℝ) (i : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerreWeight (a+i) x = laguerreWeight a x * x^i := by
  unfold laguerreWeight
  rw [show a+(i:ℝ)-1=(a-1)+(i:ℝ) by ring, Real.rpow_add hx, Real.rpow_natCast]
  ring

lemma laguerre_evaluation_determinant {n : ℕ} (a : ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    (evaluationMatrix (laguerrePhi n a) x).det =
      (∏ i, (laguerreWeight a (x i) : ℂ)) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ)) := by
  have he : evaluationMatrix (laguerrePhi n a) x =
      Matrix.of (fun i j => (laguerreWeight a (x j) : ℂ) *
        (Matrix.vandermonde (fun i => (x i : ℂ))).transpose i j) := by
    ext i j
    simp only [evaluationMatrix, laguerrePhi, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.vandermonde_apply, laguerreWeight_shift_nat a i.val (hx j),
      Complex.ofReal_mul, Complex.ofReal_pow]
  rw [he, Matrix.det_mul_row, Matrix.det_transpose, Matrix.det_vandermonde]

lemma vandermonde_schur_density (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    ((∏ i, (laguerreWeight a (x i) : ℂ)) *
      ∏ i, ∏ j ∈ Finset.Ioi i, ((x j : ℂ) - (x i : ℂ))) *
        schurProduct (fun i => (x i : ℂ)) = (laguerreDensity n a x : ℂ) := by
  simp only [laguerreDensity, Complex.ofReal_mul, Complex.ofReal_prod, mul_assoc, schurProduct]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [schurEntry, pairKernel, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_add]
  rw [add_comm (x j : ℂ) (x i : ℂ)]
  ring

def laguerreEvenIntegrand (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : ℂ :=
  (evaluationMatrix (laguerrePhi n a) x).det *
    pfaffian n (schurMatrix (fun i => (x i : ℂ)))

def laguerreOddIntegrand (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : ℂ :=
  (evaluationMatrix (laguerrePhi n a) x).det *
    pfaffian (n+1) (border (schurMatrix (fun i => (x i : ℂ))) (fun _ => 1))

lemma laguerreEvenIntegrand_eq {n : ℕ} (hn : Even n) (a : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
    laguerreEvenIntegrand n a x = laguerreDensity n a x := by
  have hd (i j : Fin n) : (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hi : Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  rw [laguerreEvenIntegrand, pfaffian_schur_even n hn _ hd hi,
    laguerre_evaluation_determinant a hx.2, vandermonde_schur_density]

lemma laguerreOddIntegrand_eq {n : ℕ} (hn : Odd n) (a : ℝ)
    {x : Fin n → ℝ} (hx : x ∈ laguerreDomain n) :
    laguerreOddIntegrand n a x = laguerreDensity n a x := by
  have hd (i j : Fin n) : (x i : ℂ) + (x j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
    exact (add_pos (hx.2 i) (hx.2 j)).ne'
  have hi : Function.Injective (fun i => (x i : ℂ)) := Complex.ofReal_injective.comp hx.1.injective
  rw [laguerreOddIntegrand, pfaffian_schur_odd n hn _ hd hi,
    laguerre_evaluation_determinant a hx.2, vandermonde_schur_density]

lemma integral_laguerreEvenIntegrand {n : ℕ} (hn : Even n) {a : ℝ} (ha : 0 < a) :
    (∫ x, laguerreEvenIntegrand n a x ∂Measure.pi (fun _ : Fin n => μ₊)) =
      (n.factorial : ℂ) * (laguerreNormalizer n a : ℂ) := by
  have he : ∀ᵐ x ∂volume.restrict (laguerreDomain n),
      laguerreEvenIntegrand n a x = (laguerreDensity n a x : ℂ) :=
    (ae_restrict_mem (isOpen_laguerreDomain n).measurableSet).mono
      fun x hx => laguerreEvenIntegrand_eq hn a hx
  rw [integral_symmetric_ordered _
    (fun σ x => determinantPfaffian_symmetric_even hn _
      (fun r s : ℝ => schurEntry r s) (fun r s => schurEntry_swap _ _) σ x)
    (fun x hx => by
      unfold laguerreEvenIntegrand
      rw [evaluationMatrix_det_of_not_injective _ hx, zero_mul])
    (by
      have hi := (integrableOn_laguerreDensity n ha).ofReal (𝕜 := ℂ)
      simp only [RCLike.ofReal_eq_complex_ofReal] at hi
      exact hi.congr (he.mono fun _ h => h.symm))]
  rw [integral_congr_ae he, integral_complex_ofReal]
  rfl

end
end CriticalStrip

end OAI
