import OAI.Analysis.GroupDeterminants.RegularAdjoint

namespace OAI

universe uA

noncomputable section
open scoped BigOperators

namespace GroupRingDeterminant

section ProjectionLog
variable {A : Type uA} [CStarAlgebra A]

theorem cfc_projectionReweight (P : A) (hP : IsSelfAdjoint P) (a b : ℝ) :
    cfc (fun x : ℝ => a * x + b * (1 - x)) P = projectionReweight P a b := by
  rw [cfc_add P (fun x : ℝ => a * x) (fun x : ℝ => b * (1 - x))
    (by fun_prop) (by fun_prop),
    cfc_const_mul a (fun x : ℝ => x) P (by fun_prop),
    cfc_const_mul b (fun x : ℝ => 1 - x) P (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) P (by fun_prop) (by fun_prop)]
  simp [projectionReweight, cfc_id' ℝ P hP, cfc_const_one ℝ P hP]

theorem log_projectionReweight (P : A) (hP : IsSelfAdjoint P) (hPP : P * P = P)
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    CFC.log (projectionReweight P a b) =
      projectionReweight P (Real.log a) (Real.log b) := by
  have hp : IsIdempotentElem P := hPP
  have hc : ContinuousOn Real.log ((fun x : ℝ => a * x + b * (1 - x)) '' spectrum ℝ P) := by
    rintro y ⟨x, hx, rfl⟩
    rcases hp.spectrum_subset ℝ hx with h | h
    · have hx0 : x = 0 := h
      simp only [hx0, mul_zero, sub_zero, mul_one, zero_add]
      exact (Real.continuousAt_log hb).continuousWithinAt
    · have hx1 : x = 1 := h
      simp only [hx1, mul_one, sub_self, mul_zero, add_zero]
      exact (Real.continuousAt_log ha).continuousWithinAt
  rw [CFC.log, ← cfc_projectionReweight P hP a b,
    ← cfc_comp' Real.log (fun x : ℝ => a * x + b * (1 - x)) P hc (by fun_prop) hP,
    ← cfc_projectionReweight P hP (Real.log a) (Real.log b)]
  apply cfc_congr
  intro x hx
  rcases hp.spectrum_subset ℝ hx with h | h
  · have hx0 : x = 0 := h
    simp [hx0]
  · have hx1 : x = 1 := h
    simp [hx1]

end ProjectionLog

end GroupRingDeterminant

end

end OAI
