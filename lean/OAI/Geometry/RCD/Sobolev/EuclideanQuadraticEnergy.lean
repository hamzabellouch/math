import OAI.Geometry.RCD.Sobolev.GradientEnergyFromDensity
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Exact quadratic expansion of Euclidean gradient energies -/

open MeasureTheory
open scoped RealInnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_quadratic_energy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} (U V : α → Euclidean n)
    (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hiU : Integrable (fun x => ‖U x‖^2) μ) (hiV : Integrable (fun x => ‖V x‖^2) μ)
    (t : ℝ) :
    Integrable (fun x => inner ℝ (U x) (V x)) μ ∧
    Integrable (fun x => ‖U x+t • V x‖^2) μ ∧
    (∫ x, ‖U x+t • V x‖^2 ∂μ)=
      (∫ x, ‖U x‖^2 ∂μ)+2*t*(∫ x, inner ℝ (U x) (V x) ∂μ)+t^2*(∫ x, ‖V x‖^2 ∂μ) := by
  have hcross : Integrable (fun x => inner ℝ (U x) (V x)) μ := by
    apply (hiU.add hiV).mono' (hU.inner hV)
    apply Filter.Eventually.of_forall
    intro x
    have hc := norm_inner_le_norm (𝕜 := ℝ) (U x) (V x)
    simp only [Pi.add_apply,Real.norm_eq_abs] at hc ⊢
    nlinarith [sq_nonneg (‖U x‖-‖V x‖),sq_nonneg ‖U x‖,sq_nonneg ‖V x‖]
  have he (x : α) : ‖U x+t • V x‖^2=
      ‖U x‖^2+2*t*inner ℝ (U x) (V x)+t^2*‖V x‖^2 := by
    rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hf : Integrable (fun x => ‖U x+t • V x‖^2) μ := by
    simp_rw [he]
    exact (hiU.add (hcross.const_mul (2*t))).add (hiV.const_mul (t^2))
  refine ⟨hcross,hf,?_⟩
  simp_rw [he]
  have hsum := integral_add (hiU.add (hcross.const_mul (2*t))) (hiV.const_mul (t^2))
  have hfirst := integral_add hiU (hcross.const_mul (2*t))
  simp only [Pi.add_apply] at hsum hfirst
  rw [hsum,hfirst,integral_const_mul,integral_const_mul]

end RegularPointCoordinates

end

end OAI
