import OAI.Analysis.CircleDomains.Topology.RoundBoundaryStability
import OAI.Analysis.CircleDomains.Topology.CircleFormBoundary
import OAI.Analysis.CircleDomains.Modulus.StokesBudget

namespace OAI

/-! A retained real lift converts the actual target-circuit Stokes
integral into the fixed-source boundary functional. Uniform convergence
of the maps and convergence of the terminal disks then pass the proved
finite Stokes bound to the limiting pair. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem circleFormIntegral_eq_roundBoundaryPairing
    (O : Set ℂ) (hO : IsOpen O) (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    (γ : ℝ → ℂ) (hγ : Differentiable ℝ γ) (hγO : ∀ t, γ t ∈ O)
    (v : ℝ → ℝ) (hv : Continuous v) (hproj : ∀ t, (v t : UnitAddCircle) = u (γ t))
    (c : ℂ) (r : ℝ) :
    circleFormIntegral (fun z => infDist z (closedBall c r)) u γ =
      roundDiskBoundaryPairing γ c r v :=
  circleFormIntegral_eq_real_lift hO hu _ γ hγ hγO v hv hproj

 theorem stokes_boundary_limit_bound
    (γ : ℕ → ℝ → ℂ) (γ₀ : ℝ → ℂ)
    (hγ : ∀ n, Differentiable ℝ (γ n)) (hγ₀ : Continuous γ₀)
    (O : ℕ → Set ℂ) (hO : ∀ n, IsOpen (O n))
    (u : ℕ → ℂ → UnitAddCircle) (hu : ∀ n, SmoothCircleOn (u n) (O n))
    (hγO : ∀ n t, γ n t ∈ O n)
    (v : ℝ → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hproj : ∀ n t, (v t : UnitAddCircle) = u n (γ n t))
    (c : ℕ → ℂ) (c₀ : ℂ) (hc : Tendsto c atTop (𝓝 c₀))
    (r : ℕ → ℝ) {r₀ : ℝ} (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hrr : Tendsto r atTop (𝓝 r₀))
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (he0 : Tendsto e atTop (𝓝 0))
    (hclose : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ n t) (γ₀ t) ≤ e n)
    (L E B : ℝ) (εE εA : ℕ → ℝ)
    (hεE : Tendsto εE atTop (𝓝 0)) (hεA : Tendsto εA atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      |circleFormIntegral (fun z => infDist z (closedBall (c n) (r n))) (u n) (γ n)| ≤
        Real.sqrt Real.pi * L * (E + εE n) + 2 * Real.pi * L * (B + εA n)) :
    |roundDiskBoundaryPairing γ₀ c₀ r₀ v| ≤ Real.sqrt Real.pi * L * E + 2 * Real.pi * L * B := by
  have hEq (n : ℕ) := circleFormIntegral_eq_roundBoundaryPairing (O n) (hO n) (u n) (hu n)
    (γ n) (hγ n) (hγO n) v hv.continuous (hproj n) (c n) (r n)
  have hb : ∀ᶠ n in atTop, |roundDiskBoundaryPairing (γ n) (c n) (r n) v| ≤
      Real.sqrt Real.pi * L * (E + εE n) + 2 * Real.pi * L * (B + εA n) := by
    filter_upwards [hbound] with n hn
    rwa [hEq n] at hn
  have ht := tendsto_roundDiskBoundaryPairing γ γ₀ (fun n => (hγ n).continuous) hγ₀
    c c₀ hc r hr hr₀ hrr v hv e he he0 hclose
  have hcost : Tendsto (fun n => Real.sqrt Real.pi * L * (E + εE n) +
      2 * Real.pi * L * (B + εA n)) atTop
      (𝓝 (Real.sqrt Real.pi * L * E + 2 * Real.pi * L * B)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := E)).add hεE).const_mul (Real.sqrt Real.pi * L) |>.add
        (((tendsto_const_nhds (x := B)).add hεA).const_mul (2 * Real.pi * L))
  exact le_of_tendsto_of_tendsto ht.abs hcost hb

end CircleDomainRigidity

end

end OAI
