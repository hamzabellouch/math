import OAI.NumberTheory.CubicMoment.Estimates.SmallBNonzeroVariance

namespace OAI

/-! The pure power saving for the original variance after subtraction
of its exact, height-independent zero-frequency model. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def varianceZeroMode (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (V : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ k ∈ commonRowFactors S, commonGramZeroMode S (fun b => star (β b)) V A k

lemma commonGramZeroMode_height_eq (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) {k : Eisenstein}
    (hk : primary k) (hsk : Squarefree k) :
    commonGramZeroMode S (fun b => star (dispersionAmplitude β u b)) V A k =
      commonGramZeroMode S (fun b => star (β b)) V A k := by
  rw [commonGramZeroMode_eq S hS _ V A hk hsk,commonGramZeroMode_eq S hS _ V A hk hsk]
  by_cases hks : k ∈ S
  · simp only [ite_eq_left hks,star_star]
    have hp (z : ℂ) : star z*z = ((‖z‖^2:ℝ):ℂ) := by
      simpa only [starRingEnd_apply,mul_comm,Complex.ofReal_pow] using Complex.mul_conj' z
    rw [hp,hp,dispersionAmplitude_norm_squarefree (hS k hks).1 (hS k hks).2]
  · simp only [ite_eq_right hks]

lemma variance_sub_zero_eq (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance S β u V A-varianceZeroMode S β V A =
      ∑ k ∈ commonRowFactors S,
        (commonGramBlock S (fun b => star (dispersionAmplitude β u b)) V A k-
          commonGramZeroMode S (fun b => star (dispersionAmplitude β u b)) V A k) := by
  rw [smoothedVariance_eq_commonGram S hS β u V hV hV' hA,varianceZeroMode,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [commonGramZeroMode_height_eq S hS β u V A
    (commonRowFactors_spec hS hk).1 (commonRowFactors_spec hS hk).2]

theorem smallB_variance_remainder_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u : ℝ), 65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t) V A-varianceZeroMode S β V A‖) T ≤
        K*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hbound⟩ := smallB_nonzero_variance_height_power hMV hC hHuxley V hV hV'
  refine ⟨K,hK,?_⟩
  intro S β Z A T u hZ hA hT hS
  have hA0 : 0 < A := (Real.rpow_pos_of_pos (by linarith : 0 < Z) _).trans_le hA
  simp_rw [variance_sub_zero_eq S (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩)
    β _ V hV hV' hA0]
  exact hbound S β Z A T u hZ hA hT hS

end CubicFirstMoment

end

end OAI
