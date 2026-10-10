import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailConvolution
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernels

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels

theorem convolve_rescale {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    {r : ℝ} (hr : 0 < r) (J : compatibleJets n a) :
    convolve (integrable_rescale hk hr) J = average k (-r) J := by
  have hh := Measure.integral_comp_smul_of_nonneg volume
    (fun X : Coord n => k (r⁻¹ • X) • translate (-X) J) r (hR := hr.le)
  simp only [Coord, Module.finrank_pi, Fintype.card_fin, inv_smul_smul₀ hr.ne',
    ← neg_smul] at hh
  change (∫ X, rescale k r X • translate ((-1 : ℝ) • X) J) = _
  simp only [rescale, neg_one_smul, mul_smul]
  rw [integral_smul]
  exact hh.symm

def heat {a : ℕ} (ν t : ℝ) : compatibleJets 2 a →L[ℝ] compatibleJets 2 a :=
  averageL (integrable_normal 2) (-Real.sqrt (2 * ν * t))

@[simp] theorem heat_zero {a : ℕ} (ν : ℝ) (J : compatibleJets 2 a) : heat ν 0 J = J := by
  simp [heat, averageL_apply, average_zero_scale]

theorem heat_eq_convolve {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (J : compatibleJets 2 a) : heat ν t J = convolve (integrable_kernel hν ht) J := by
  have hh := convolve_rescale (integrable_normal 2)
    (Real.sqrt_pos.mpr (show 0 < 2 * ν * t by positivity)) J
  change average (normal 2) (-Real.sqrt (2 * ν * t)) J = average (kernel ν t) (-1) J
  change average (rescale (normal 2) (Real.sqrt (2 * ν * t))) (-1) J = _ at hh
  rw [← kernel_eq_rescale hν ht] at hh
  exact hh.symm

theorem norm_heat_le {a : ℕ} (ν t : ℝ) (J : compatibleJets 2 a) : ‖heat ν t J‖ ≤ ‖J‖ :=
  norm_average_le_of_probability_kernel (integrable_normal 2) (normal_nonneg 2)
    (integral_normal 2) _ J

theorem continuous_heat {a : ℕ} (ν : ℝ) (J : compatibleJets 2 a) :
    Continuous (fun t : ℝ => heat ν t J) := by
  exact (continuous_average (integrable_normal 2) J).comp
    (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).neg

theorem value_heat {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (J : compatibleJets 2 a) (X : Coord 2) :
    value (heat ν t J) X = ∫ Y, kernel ν t Y * value J (X - Y) := by
  rw [heat_eq_convolve hν ht J, value_convolve]

end VelocityDetection.TailSpace.Jets
end

end OAI
