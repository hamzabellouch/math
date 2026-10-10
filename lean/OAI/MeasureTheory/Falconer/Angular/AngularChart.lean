import OAI.MeasureTheory.Falconer.Geometry.NonstationaryGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

/-!
# A normalized affine line in a spherical chart

Differentiation in a gnomonic chart is the tangential projection of the
coordinate direction divided by the normalization. This connects the
failed perpendicular test to an ordinary one-variable phase derivative.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalizedLine (a t : E) (u : ℝ) : E :=
  ‖a + u • t‖⁻¹ • (a + u • t)

theorem normalizedLine_norm (a t : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    ‖normalizedLine a t u‖ = 1 := by
  rw [normalizedLine,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

private theorem norm_line_hasDerivAt (a t : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    HasDerivAt (fun x : ℝ => ‖a + x • t‖)
      (inner ℝ (a + u • t) t / ‖a + u • t‖) u := by
  have hz : HasDerivAt (fun x : ℝ => a + x • t) t u := by
    simpa using ((hasDerivAt_id u).smul_const t).const_add a
  have hsq := hz.norm_sq
  have hh := hsq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  have he : (2 * inner ℝ (a + u • t) t) / (2 * Real.sqrt (‖a+u•t‖^2)) =
      inner ℝ (a+u•t) t / ‖a+u•t‖ := by
    rw [Real.sqrt_sq (norm_nonneg _)]
    ring
  rw [he] at hh
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hh

theorem normalizedLine_hasDerivAt (a t : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    HasDerivAt (normalizedLine a t)
      (‖a + u • t‖⁻¹ • perpendicularPart (normalizedLine a t u) t) u := by
  have hz : HasDerivAt (fun x : ℝ => a + x • t) t u := by
    simpa using ((hasDerivAt_id u).smul_const t).const_add a
  have hi := (norm_line_hasDerivAt a t hne).inv (norm_ne_zero_iff.mpr hne)
  have hh := hi.smul hz
  convert hh using 1
  · rfl
  · simp only [normalizedLine,perpendicularPart,real_inner_smul_left,smul_sub,smul_smul,
      div_eq_mul_inv,neg_mul]
    module

theorem normalizedLine_phase_hasDerivAt (a t Δ : E) {u : ℝ} (hne : a + u • t ≠ 0) :
    HasDerivAt (fun x => inner ℝ (normalizedLine a t x) Δ)
      (‖a+u•t‖⁻¹ * inner ℝ (perpendicularPart (normalizedLine a t u) t) Δ) u := by
  simpa only [inner_zero_right,add_zero,zero_add,real_inner_smul_left] using
    (normalizedLine_hasDerivAt a t hne).inner ℝ (hasDerivAt_const u Δ)

/-- The normalization costs at most two in the failed-test lower bound. -/
theorem normalizedLine_phase_nonstationary (a t Δ : E) {u τ : ℝ}
    (hne : a+u•t ≠ 0) (hnorm : ‖a+u•t‖ ≤ 2) (hτ : 0 ≤ τ)
    (hderiv : τ/2 ≤ |inner ℝ (perpendicularPart (normalizedLine a t u) t) Δ|) :
    τ/4 ≤ |deriv (fun x => inner ℝ (normalizedLine a t x) Δ) u| := by
  rw [(normalizedLine_phase_hasDerivAt a t Δ hne).deriv,abs_mul,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne))]
  have hhalf : (1/2 : ℝ) ≤ ‖a+u•t‖⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (norm_pos_iff.mpr hne) hnorm
  calc
    τ/4 = (1/2 : ℝ)*(τ/2) := by ring
    _ ≤ ‖a+u•t‖⁻¹ * |inner ℝ (perpendicularPart (normalizedLine a t u) t) Δ| :=
      mul_le_mul hhalf hderiv (by positivity) (by positivity)

end Falconer

end OAI
