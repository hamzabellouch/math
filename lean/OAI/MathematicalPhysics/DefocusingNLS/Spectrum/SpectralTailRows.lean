import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingRadialRows
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTailEulerPhysical

namespace OAI

/-! The physical row comparison only needs smoothness and boundedness on a tail. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

theorem homogeneousOutgoingRows_tail_comparison
    (U W : ℝ → V) (T R : ℝ → End) (n : ℕ) (c K M : ℝ)
    (R₀ : ℝ) (hR₀ : 0<R₀) (hU : ContDiffOn ℝ ∞ U (Ioi R₀)) (hc : 0 < c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hbound : ∀ r, R₀≤r → ‖U r‖ ≤ M)
    (hrow : ∀ᶠ t in atTop, ∀ w : V,
      c * Real.exp (2 * (n : ℝ) * t) * ‖w‖ ≤ ‖T t w‖)
    (hR : ∀ᶠ t in atTop, ‖R t‖ ≤ K)
    (hid : ∀ᶠ t in atTop,
      homogeneousEulerDeriv (fun s => U (Real.exp s)) (n + 1) t =
        T t (Real.exp t • W (Real.exp t)) + R t (U (Real.exp t))) :
    ∀ᶠ r in atTop, r ^ (2 * (n : ℝ)) * homogeneousPairEnergy (W r) ≤
      (4 / c ^ 2) * homogeneousPairEnergy (iteratedDeriv (n + 1) U r) +
        (4 / c ^ 2) * (K * M) ^ 2 * r ^ (-2 * ((n + 1 : ℕ) : ℝ)) := by
  have hall := hrow.and (hR.and hid)
  have hlog := Real.tendsto_log_atTop.eventually hall
  filter_upwards [hlog, eventually_gt_atTop R₀] with r h hr₁
  have hr : 0<r := hR₀.trans hr₁
  have hlogr : Real.log R₀<Real.log r := Real.log_lt_log hR₀ hr₁
  have hUt : ContDiffOn ℝ ∞ U (Ioi (Real.exp (Real.log R₀))) := by
    simpa only [Real.exp_log hR₀] using hU
  have he2 : Real.exp (2 * (n : ℝ) * Real.log r) = r ^ (2 * n) := by
    rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hr]
  have heN : Real.exp (((n + 1 : ℕ) : ℝ) * Real.log r) = r ^ (n + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log hr]
  have hident := h.2.2
  rw [homogeneousEulerDeriv_physical_tail U (Real.log R₀) hUt (n+1) (Real.log r) hlogr,
    heN,Real.exp_log hr] at hident
  apply homogeneousLogRow_energy_comparison (U r) (W r)
    (iteratedDeriv (n + 1) U r) (T (Real.log r)) (R (Real.log r))
    r c K M n hr hc hK hM
  · simpa only [he2, Real.exp_log hr] using h.1 (r • W r)
  · exact hident
  · exact h.2.1
  · exact hbound r hr₁.le

end DefocusingNLS

end OAI
