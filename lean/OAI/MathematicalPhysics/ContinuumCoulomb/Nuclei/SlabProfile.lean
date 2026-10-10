import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabPlanarTail

namespace OAI

/-! Quantitative removal of the vertical regularization. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

def slabRegularizedProfile (epsilon S z : ℝ) : ℝ :=
  ∫ w in (-S)..S, Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2)

theorem slab_sqrt_regularization (epsilon a : ℝ) :
    0 ≤ Real.sqrt (epsilon^2+a^2)-|a| ∧
      Real.sqrt (epsilon^2+a^2)-|a| ≤ |epsilon| := by
  have hp : 0 ≤ epsilon^2+a^2 := by positivity
  have hl : |a| ≤ Real.sqrt (epsilon^2+a^2) := by
    rw [← Real.sqrt_sq_eq_abs a]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg epsilon])
  constructor
  · linarith
  · have hs := Real.sq_sqrt hp
    have he := sq_abs epsilon
    have ha := sq_abs a
    nlinarith [Real.sqrt_nonneg (epsilon^2+a^2), abs_nonneg epsilon,
      abs_nonneg a, mul_nonneg (abs_nonneg epsilon) (abs_nonneg a)]

theorem slabRegularizedProfile_error {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    (epsilon : ℝ) : |slabRegularizedProfile epsilon S z-z^2| ≤ 4*S*|epsilon| := by
  have hc : Continuous (fun w : ℝ => Real.sqrt (epsilon^2+(z-w)^2)-
      Real.sqrt (epsilon^2+w^2)) := by fun_prop
  have hd : Continuous (fun w : ℝ => |z-w|-|w|) := by fun_prop
  rw [slabRegularizedProfile, ← slab_absolute_difference_integral hS hz,
    ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  have hbound (w : ℝ) :
      ‖(Real.sqrt (epsilon^2+(z-w)^2)-Real.sqrt (epsilon^2+w^2))-(|z-w|-|w|)‖ ≤
        2*|epsilon| := by
    obtain ⟨ha0,ha1⟩ := slab_sqrt_regularization epsilon (z-w)
    obtain ⟨hb0,hb1⟩ := slab_sqrt_regularization epsilon w
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -S) (b := S) (fun w _ => hbound w)
  rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith : 0 ≤ S+S)] at h
  convert h using 1
  ring

theorem slabRegularizedProfile_tendsto {S z : ℝ} (hS : 0 ≤ S) (hz : |z| ≤ S)
    {epsilon : ℕ → ℝ} (hepsilon : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => slabRegularizedProfile (epsilon n) S z) atTop (𝓝 (z^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro delta hdelta
  have hlim : Tendsto (fun n => 4*S*|epsilon n|) atTop (𝓝 0) := by
    simpa using hepsilon.abs.const_mul (4*S)
  filter_upwards [((tendsto_order.1 hlim).2 delta hdelta)] with n hn
  rw [Real.dist_eq]
  exact (slabRegularizedProfile_error hS hz (epsilon n)).trans_lt hn

end ContinuumCoulomb

end

end OAI
