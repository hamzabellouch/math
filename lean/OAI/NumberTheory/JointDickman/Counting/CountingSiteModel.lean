import OAI.NumberTheory.JointDickman.Counting.CountingCandidateComparison
import OAI.NumberTheory.JointDickman.Counting.LagSquareSum
import OAI.NumberTheory.JointDickman.Probability.SingularSeriesMoments

namespace OAI

/-! # The symmetric finite-feature block model and its lag envelope -/
namespace JointDickman
open Finset Classical

noncomputable def countingSiteModel (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) : ℝ :=
  if i < k then
    if H < k.val-i.val ∧ k.val-i.val < T then
      countingCandidateModel P m B L (k.val-i.val) τ C c D T σ a.val b.val else 0
  else if k < i then
    if H < i.val-k.val ∧ i.val-k.val < T then
      countingCandidateModel P m B L (i.val-k.val) τ C c D T σ b.val a.val else 0
  else 0

theorem countingSiteModel_diag (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteModel P m B L T H M τ C c D σ i i a b = 0 := by
  simp only [countingSiteModel,lt_self_iff_false,ite_false]

theorem countingSiteModel_symm (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteModel P m B L T H M τ C c D σ i k a b =
      countingSiteModel P m B L T H M τ C c D σ k i b a := by
  rcases lt_trichotomy i k with h | rfl | h
  · simp only [countingSiteModel,h,not_lt_of_ge h.le,ite_true,ite_false]
  · rw [countingSiteModel_diag,countingSiteModel_diag]
  · simp only [countingSiteModel,h,not_lt_of_ge h.le,ite_true,ite_false]

theorem countingCandidateModel_lag_bound
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {T η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hlag : η*T ≤ j)
    (hbound : ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (a b : Finset ℕ) :
    |countingCandidateModel P m B L j τ C c D T σ a b| ≤
      (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 j := by
  have hjr : (0 : ℝ) < j := (mul_pos hη hT).trans_le hlag
  have hj : 0 < j := by exact_mod_cast hjr
  have hsf : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  have he : singularSeries j/(j : ℝ) ≤ singularFactor 24 j/(η*T) :=
    (div_le_div_of_nonneg_right (singularSeries_le_singularFactor hMP hj) hjr.le).trans
      (div_le_div_of_nonneg_left hsf (mul_pos hη hT) hlag)
  calc
    _ ≤ (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*C₀ :=
      countingCandidateModel_bound P m B L j τ C c D T σ C₀ (singularSeries_bounds hMP j).1 hbound a b
    _ ≤ (independentRootMean B L τ C*(singularFactor 24 j/(η*T)))*C₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (independentRootMean_nonneg ..)) hC₀
    _ = _ := by ring

theorem countingSiteModel_lag_envelope
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hf (i k : Fin M) (hik : i < k) (a b : (auxiliaryPrimes B).powerset) :
      |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
    rw [countingSiteModel,ite_eq_left hik,Nat.dist_eq_sub_of_le hik.le]
    by_cases ha : H < k.val-i.val ∧ k.val-i.val < T
    · rw [ite_eq_left ha,ite_eq_left ⟨ne_of_lt hik,ha.2⟩]
      apply countingCandidateModel_lag_bound hMP P m B L _ τ C c D hTr hη hC₀ _ (hbound _ ha.1 ha.2)
      exact hH.trans (by exact_mod_cast ha.1.le)
    · rw [ite_eq_right ha,abs_zero]
      split_ifs
      · exact mul_nonneg (div_nonneg (mul_nonneg (independentRootMean_nonneg ..) hC₀)
          (mul_pos hη hTr).le) (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
      · exact le_rfl
  rcases lt_trichotomy i k with h | rfl | h
  · exact hf i k h a b
  · simp only [countingSiteModel_diag,ne_eq,not_true_eq_false,false_and,ite_false,abs_zero,le_refl]
  · rw [countingSiteModel_symm, Nat.dist_comm i.val k.val]
    have hh := hf k i h b a
    simpa only [ne_comm] using hh

end JointDickman

end OAI
