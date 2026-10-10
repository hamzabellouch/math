import OAI.Probability.FirstPassage.LatticeSwap

namespace OAI

namespace PlanarFPP
open MeasureTheory

lemma norm_differentiable_smul (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (u : Plane) (t : ℝ) (ht : t ≠ 0) (hu : DifferentiableAt ℝ μ u) :
    DifferentiableAt ℝ μ (t • u) := by
  have hi : DifferentiableAt ℝ μ (t⁻¹ • (t • u)) := by simpa [smul_smul,ht] using hu
  have hc := hi.comp (t • u) (differentiableAt_id.const_smul t⁻¹)
  have hd := hc.const_mul |t|
  have he : (fun z : Plane => |t| *μ (t⁻¹ • z))=μ := by
    funext z
    rw [hμ.homogeneous,abs_inv,← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr ht),one_mul]
  simpa only [Function.comp_def,he] using hd

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_differentiable_horizontal (henv : ExponentialEnvironment P τ)
    (v : Plane) (hv : v ≠ 0) (hdom : |v 1| ≤ |v 0|) :
    DifferentiableAt ℝ actualSourceTimeConstant v := by
  have hx : v 0 ≠ 0 := by
    intro hx
    have hy : v 1=0 := by simpa [hx] using hdom
    apply hv
    ext i
    fin_cases i <;> simp [hx,hy]
  have hb : |v 1/v 0| ≤ 1 := by rw [abs_div]; exact (div_le_one (abs_pos.mpr hx)).mpr hdom
  have he : v 0 • direction (v 1/v 0)=v := by
    ext i
    fin_cases i <;> simp [direction,PiLp.smul_apply]
    field_simp
  rw [← he]
  exact norm_differentiable_smul _ actualSourceTimeConstant_norm _ _ hx
    (actual_direction_differentiable henv _ hb)

theorem actual_differentiable_away (henv : ExponentialEnvironment P τ) :
    DifferentiableAwayFromOrigin actualSourceTimeConstant := by
  intro v hv
  have hd : DifferentiableAt ℝ actualSourceTimeConstant v := by
    by_cases hh : |v 1| ≤ |v 0|
    · exact actual_differentiable_horizontal henv v hv hh
    · have hsv : swapPlane v ≠ 0 := by intro h; apply hv; exact swapPlane.injective (by simpa using h)
      have hdom : |swapPlane v 1| ≤ |swapPlane v 0| := by simpa using (le_of_not_ge hh)
      have hs := actual_differentiable_horizontal henv (swapPlane v) hsv hdom
      have hc := hs.comp v swapPlane.toContinuousLinearEquiv.differentiableAt
      have he : (fun z => actualSourceTimeConstant (swapPlane z))=actualSourceTimeConstant :=
        funext (actualSourceTimeConstant_swap henv)
      simpa only [Function.comp_def,he] using hc
  exact ⟨fderiv ℝ actualSourceTimeConstant v,hd.hasFDerivAt⟩

end PlanarFPP

end OAI
