import OAI.NumberTheory.JointDickman.Counting.CountingModelEnvelope
import OAI.NumberTheory.JointDickman.Counting.DistanceLagSum
import OAI.NumberTheory.JointDickman.Amplification.SingularSeriesApproximation

namespace OAI

/-! # Replacing the singular series in the actual finite-feature graph -/
namespace JointDickman
open Finset Classical

noncomputable def countingCandidateWithSeries (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) (S R : Finset ℕ) : ℝ :=
  (independentRootMean B L τ C*(F j/(j : ℝ)))*
    subsetPrimeModel B (fun x y => countingPrimeKernel P m B j c D T σ y x) S R

noncomputable def countingSiteWithSeries (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  if i < k then
    if H < k.val-i.val ∧ k.val-i.val < T then
      countingCandidateWithSeries F P m B L (k.val-i.val) τ C c D T σ a.val b.val else 0
  else if k < i then
    if H < i.val-k.val ∧ i.val-k.val < T then
      countingCandidateWithSeries F P m B L (i.val-k.val) τ C c D T σ b.val a.val else 0
  else 0

theorem countingSiteWithSeries_original
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ) :
    countingSiteWithSeries singularSeries P m B L T H M τ C c D σ =
      countingSiteModel P m B L T H M τ C c D σ := rfl

theorem countingCandidateWithSeries_difference
    (F G : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {T σ K : ℝ}
    (hK : ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K)
    (S R : Finset ℕ) :
    |countingCandidateWithSeries F P m B L j τ C c D T σ S R-
      countingCandidateWithSeries G P m B L j τ C c D T σ S R| ≤
      (independentRootMean B L τ C/(j : ℝ))*|F j-G j| *K := by
  have hr := independentRootMean_nonneg B L τ C
  have he : countingCandidateWithSeries F P m B L j τ C c D T σ S R-
      countingCandidateWithSeries G P m B L j τ C c D T σ S R =
      (independentRootMean B L τ C/(j : ℝ))*(F j-G j)*
        subsetPrimeModel B (fun x y => countingPrimeKernel P m B j c D T σ y x) S R := by
    unfold countingCandidateWithSeries
    ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg (div_nonneg hr (Nat.cast_nonneg j))]
  exact mul_le_mul_of_nonneg_left (hK _ _) (mul_nonneg (by positivity) (abs_nonneg _))

theorem countingSiteWithSeries_difference
    (F G : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {σ η K : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hK : 0 ≤ K) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteWithSeries F P m B L T H M τ C c D σ i k a b-
      countingSiteWithSeries G P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*K/(η*T))*|F (Nat.dist i.val k.val)-G (Nat.dist i.val k.val)|
      else 0 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hr := independentRootMean_nonneg B L τ C
  have hc (j : ℕ) (hj : H < j) (hjt : j < T) (a b : Finset ℕ) :
      |countingCandidateWithSeries F P m B L j τ C c D T σ a b-
        countingCandidateWithSeries G P m B L j τ C c D T σ a b| ≤
        (independentRootMean B L τ C*K/(η*T))*|F j-G j| := by
    have hjr : η*(T : ℝ) ≤ j := hH.trans (by exact_mod_cast hj.le)
    have hj0 : (0 : ℝ) < j := (mul_pos hη hTr).trans_le hjr
    have hdiv := one_div_le_one_div_of_le (mul_pos hη hTr) hjr
    have hmul := mul_le_mul_of_nonneg_left hdiv (mul_nonneg (mul_nonneg hr hK) (abs_nonneg (F j-G j)))
    calc
      _ ≤ (independentRootMean B L τ C/(j : ℝ))*|F j-G j| *K :=
        countingCandidateWithSeries_difference F G P m B L j τ C c D (hbound j hj hjt) a b
      _ ≤ _ := by convert hmul using 1 <;> ring
  unfold countingSiteWithSeries
  rcases lt_trichotomy i k with hik | rfl | hki
  · rw [ite_eq_left hik,ite_eq_left hik,Nat.dist_eq_sub_of_le hik.le]
    by_cases h : H < k.val-i.val ∧ k.val-i.val < T
    · rw [ite_eq_left h,ite_eq_left h,ite_eq_left ⟨ne_of_lt hik,h.2⟩]
      exact hc _ h.1 h.2 _ _
    · rw [ite_eq_right h,ite_eq_right h,sub_self,abs_zero]
      split_ifs <;> positivity
  · simp
  · rw [ite_eq_right (not_lt_of_ge hki.le),ite_eq_right (not_lt_of_ge hki.le),ite_eq_left hki,ite_eq_left hki,
      Nat.dist_eq_sub_of_le_right hki.le]
    by_cases h : H < i.val-k.val ∧ i.val-k.val < T
    · rw [ite_eq_left h,ite_eq_left h,ite_eq_left ⟨Ne.symm (ne_of_lt hki),h.2⟩]
      exact hc _ h.1 h.2 _ _
    · rw [ite_eq_right h,ite_eq_right h,sub_self,abs_zero]
      split_ifs <;> positivity

theorem countingSiteWithSeries_cut_error
    (F G : ℕ → ℝ) (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {σ η K R δ : ℝ}
    (hT : 0 < T) (hM : 0 < M) (hη : 0 < η) (hK : 0 ≤ K)
    (hroot : independentRootMean B L τ C ≤ R) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K)
    (hmean : ∑ j ∈ Ioc 0 T, |F j-G j| ≤ δ*T)
    (x : Fin M → (auxiliaryPrimes B).powerset) :
    kernelCutNorm (realizedSiteKernel
      (fun i k a b => countingSiteWithSeries F P m B L T H M τ C c D σ i k a b-
        countingSiteWithSeries G P m B L T H M τ C c D σ i k a b) x) ≤ 2*R*K*δ/η := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hr := independentRootMean_nonneg B L τ C
  have hrow (i : Fin M) :
      (∑ k, |countingSiteWithSeries F P m B L T H M τ C c D σ i k (x i) (x k)-
        countingSiteWithSeries G P m B L T H M τ C c D σ i k (x i) (x k)|) ≤
        2*R*K*δ/η := by
    calc
      _ ≤ ∑ k, if i ≠ k ∧ Nat.dist i.val k.val < T then
          (independentRootMean B L τ C*K/(η*T))*|F (Nat.dist i.val k.val)-G (Nat.dist i.val k.val)| else 0 :=
        sum_le_sum (fun k _ => countingSiteWithSeries_difference F G P m B L T H M τ C c D
          hT hη hK hH hbound i k (x i) (x k))
      _ = (independentRootMean B L τ C*K/(η*T))*
          (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
            |F (Nat.dist i.val k.val)-G (Nat.dist i.val k.val)| else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        split_ifs <;> simp
      _ ≤ (independentRootMean B L τ C*K/(η*T))*(2*(δ*T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (distance_lag_sum i T (fun j => |F j-G j|) (fun _ => abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hmean (by norm_num))
      _ ≤ (R*K/(η*T))*(2*(δ*T)) := by
        have hδT : 0 ≤ δ*(T : ℝ) := (sum_nonneg (fun j _ => abs_nonneg (F j-G j))).trans hmean
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hK) (by positivity)
      _ = _ := by field_simp
  apply (kernelCutNorm_le_absolute_mass _).trans
  unfold kernelAbsoluteMass realizedSiteKernel
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  calc
    _ ≤ ∑ _i : Fin M, 2*R*K*δ/η := sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp; ring

/-- A fixed finite residue function suffices uniformly for all block sizes. -/
theorem countingSiteModel_periodic_approximation
    (hMP : PublishedInputs.PrimeProductMertensInput) {R K η ε : ℝ}
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hη : 0 < η) (hε : 0 < ε) :
    ∃ (q : ℕ) (_ : NeZero q) (F : ZMod q → ℝ),
      ∀ (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
        (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
        (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ),
        0 < T → 0 < M → independentRootMean B L τ C ≤ R → η*T ≤ H →
        (∀ j : ℕ, H < j → j < T →
          ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K) →
        ∀ x : Fin M → (auxiliaryPrimes B).powerset,
        kernelCutNorm (realizedSiteKernel
          (fun i k a b => countingSiteModel P m B L T H M τ C c D σ i k a b-
            countingSiteWithSeries (fun j => F (j : ZMod q)) P m B L T H M τ C c D σ i k a b) x) ≤ ε := by
  let δ := ε*η/(2*(R+1)*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨q,hq,F,hF⟩ := singularSeries_periodic_approximation hMP hδ
  refine ⟨q,hq,F,?_⟩
  intro P m B L T H M τ C c D σ hT hM hroot hH hbound x
  rw [← countingSiteWithSeries_original]
  apply (countingSiteWithSeries_cut_error singularSeries (fun j => F (j : ZMod q))
    P m B L T H M τ C c D hT hM hη hK hroot hH hbound (hF T) x).trans
  have hprod : R*K ≤ (R+1)*(K+1) := by nlinarith
  calc
    2*R*K*δ/η = ε*(R*K/((R+1)*(K+1))) := by dsimp [δ]; field_simp
    _ ≤ ε*1 := mul_le_mul_of_nonneg_left
      ((div_le_one (by positivity : 0 < (R+1)*(K+1))).mpr hprod) hε.le
    _ = ε := mul_one _

end JointDickman

end OAI
