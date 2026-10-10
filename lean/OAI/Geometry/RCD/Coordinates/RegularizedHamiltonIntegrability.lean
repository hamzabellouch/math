import OAI.Geometry.RCD.Transport.ShiftedEntropyBounds
import OAI.Geometry.RCD.Heat.LocalLogarithmicGradient

namespace OAI

/-! # Integrability for regularized Hamilton tests -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem shifted_log_gap_integrableOn (f : Lp ℝ 2 μ) {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, f x∈Icc 0 (A:ℝ)) {s : Set X} (hs : μ s<∞) :
    IntegrableOn (fun x => (ε+f x)*(Real.log (ε+A)-Real.log (ε+f x))) s μ := by
  have hm : AEStronglyMeasurable (fun x => (ε+f x)*(Real.log (ε+A)-Real.log (ε+f x))) μ :=
    (aestronglyMeasurable_const.add (Lp.aestronglyMeasurable f)).mul
      (aestronglyMeasurable_const.sub
        ((aestronglyMeasurable_const.add (Lp.aestronglyMeasurable f)).aemeasurable.log.aestronglyMeasurable))
  apply IntegrableOn.of_bound hs hm.restrict ((ε+A)*(Real.log (ε+A)-Real.log ε))
  filter_upwards [ae_restrict_of_ae hf] with x hx
  have hp : 0<ε+f x := add_pos_of_pos_of_nonneg hε hx.1
  have hlog0 : 0≤Real.log (ε+A)-Real.log (ε+f x) :=
    sub_nonneg.mpr (Real.log_le_log hp (add_le_add le_rfl hx.2))
  have hlogε : Real.log ε≤Real.log (ε+f x) :=
    Real.log_le_log hε (le_add_of_nonneg_right hx.1)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.le hlog0)]
  exact mul_le_mul (add_le_add le_rfl hx.2) (sub_le_sub_left hlogε _)
    hlog0 (add_nonneg hε.le A.coe_nonneg)

variable [MetricSpace X] [BorelSpace X] (hQ : QuadraticCheegerEnergy μ)

theorem regularized_gamma_integrable (u : SobolevSpace μ hQ) {ε : ℝ} (hε : 0<ε)
    (hu : ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ hQ u x) (c : ℝ) :
    Integrable (fun x => c*localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x)) μ := by
  have hb : ∀ᵐ x ∂μ, ‖(ε+SobolevSpace.toLp μ hQ u x)⁻¹‖≤ε⁻¹ := by
    filter_upwards [hu] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (add_nonneg hε.le hx))]
    exact inv_anti₀ hε (le_add_of_nonneg_right hx)
  have hi := (localGamma_memL1 μ hQ u u).bdd_mul
    ((aestronglyMeasurable_const.add (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ u))).aemeasurable.inv.aestronglyMeasurable) hb
  convert hi.const_mul c using 1
  funext x
  change c*localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x) =
    c*((ε+SobolevSpace.toLp μ hQ u x)⁻¹*localGamma μ hQ u u x)
  ring

end RegularPointCoordinates

end

end OAI
