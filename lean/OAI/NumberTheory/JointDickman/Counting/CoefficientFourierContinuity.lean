import OAI.NumberTheory.JointDickman.Counting.SmallMajorCoefficient
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! # Continuity of the actual coefficient Fourier profile -/

namespace JointDickman
open MeasureTheory Filter Set

theorem continuous_phase_transform {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun ξ : ℝ => ∫ s : ℝ, f s*additivePhase (-ξ*s)) := by
  apply continuous_of_dominated (bound := fun s => ‖f s‖)
  · intro ξ
    exact hf.aestronglyMeasurable.mul
      (continuous_additivePhase.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro ξ
    exact Eventually.of_forall (fun s => by rw [norm_mul,norm_additivePhase,mul_one])
  · exact hf.norm
  · exact Eventually.of_forall (fun s => continuous_const.mul
      (continuous_additivePhase.comp (continuous_id.neg.mul continuous_const)))

theorem coefficient_scaled_density_continuousOn (c : ℕ → ℝ) (H B : ℕ)
    (hB : 0 < B) {a b X : ℝ} (hX : 0 < X) (haX : 1 < a*X) :
    ContinuousOn (fun s => coefficientDensity c H B (Real.log (s*X)/B)) (Icc a b) := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have heq : (fun s => coefficientDensity c H B (Real.log (s*X)/B)) =
      fun s => coefficientScale B*roughDensityPolynomial c
        (Nat.primesLE (auxiliaryCutoff B)) (1/2) H (Real.log (s*X)) := by
    funext s
    simp only [coefficientDensity,mul_div_cancel₀ _ hB0]
  rw [heq]
  intro s hs
  have hsX : 1 < s*X := haX.trans_le (mul_le_mul_of_nonneg_right hs.1 hX.le)
  have hm : ContinuousAt (fun t : ℝ => t*X) s := continuousAt_id.mul_const X
  have hl : ContinuousAt (fun t : ℝ => Real.log (t*X)) s :=
    ContinuousAt.comp (f := fun t : ℝ => t*X) (x := s)
      (Real.continuousAt_log (by linarith : s*X ≠ 0)) hm
  have hp := ContinuousAt.comp (f := fun t : ℝ => Real.log (t*X)) (x := s)
    (roughDensityPolynomial_continuousAt c (Nat.primesLE (auxiliaryCutoff B)) (1/2) H
      (Real.log_pos hsX)) hl
  exact (continuousAt_const.mul hp).continuousWithinAt

theorem coefficientFourierTransform_continuous (c : ℕ → ℝ) (H B : ℕ)
    (hB : 0 < B) {a b X : ℝ} (hX : 0 < X) (haX : 1 < a*X)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hsupp : ∀ s, s ≤ a ∨ b < s → w s = 0) :
    Continuous (coefficientFourierTransform c H B X w) := by
  let f : ℝ → ℂ := fun s =>
    (w s : ℂ)*(coefficientDensity c H B (Real.log (s*X)/B) : ℂ)
  have hc : ContinuousOn f (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hw.continuousOn).mul
      (Complex.continuous_ofReal.comp_continuousOn
        (coefficient_scaled_density_continuousOn c H B hB hX haX))
  have hi : Integrable f := (hc.integrableOn_compact isCompact_Icc).integrable_of_forall_notMem_eq_zero
    (fun s hs => by
      have h : s ≤ a ∨ b < s := by
        by_cases hsa : s ≤ a
        · exact Or.inl hsa
        · exact Or.inr (lt_of_not_ge (fun hsb => hs ⟨(lt_of_not_ge hsa).le,hsb⟩))
      simp [f,hsupp s h])
  exact continuous_phase_transform hi

end JointDickman

end OAI
