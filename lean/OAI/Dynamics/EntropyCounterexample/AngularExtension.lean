import OAI.Dynamics.EntropyCounterexample.AngularDerivative

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340

theorem eventually_zero_comp_inv {f : ℂ → ℂ} (hf : HasCompactSupport f)
    (hzero : f 0 = 0) :
    (fun z : ℂ => f z⁻¹) =ᶠ[𝓝 0] (fun _ => 0) := by
  change ∀ᶠ z : ℂ in 𝓝 0, f z⁻¹ = 0
  rw [← nhdsNE_sup_pure (0 : ℂ), eventually_sup]
  constructor
  · have hinv : Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] 0) (coclosedCompact ℂ) := by
      simpa only [Filter.coclosedCompact_eq_cocompact,
        ← Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_nhdsNE_zero (α := ℂ))
    exact hinv.eventually (hasCompactSupport_iff_eventuallyEq.mp hf)
  · simpa using hzero

theorem contDiff_comp_inv_of_compactSupport {f : ℂ → ℂ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hcomp : HasCompactSupport f) (hzero : f 0 = 0) :
    ContDiff ℝ n (fun z : ℂ => f z⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact (contDiffAt_const : ContDiffAt ℝ n (fun _ : ℂ => (0 : ℂ)) 0).congr_of_eventuallyEq (eventually_zero_comp_inv hcomp hzero)
  · exact hf.contDiffAt.comp z (contDiffAt_id.inv hz)

def planeZeroExtension (f : ℂ → ℂ) (z : OnePoint ℂ) : ℂ := z.elim 0 f

@[simp] theorem planeZeroExtension_infty (f : ℂ → ℂ) :
    planeZeroExtension f ∞ = 0 := rfl

@[simp] theorem planeZeroExtension_coe (f : ℂ → ℂ) (z : ℂ) :
    planeZeroExtension f (z : OnePoint ℂ) = f z := rfl

theorem continuous_planeZeroExtension {f : ℂ → ℂ} (hf : Continuous f)
    (hcomp : HasCompactSupport f) : Continuous (planeZeroExtension f) := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Tendsto f (coclosedCompact ℂ) (𝓝 (0 : ℂ))
    exact Tendsto.congr' (hasCompactSupport_iff_eventuallyEq.mp hcomp).symm
      tendsto_const_nhds
  · exact hf

theorem continuous_cutoff_angular_onePoint {χ : ℂ → ℂ} {n : WithTop ℕ∞}
    (hχ : ContDiff ℝ n χ) (hcomp : HasCompactSupport χ)
    (hzero : ∀ᶠ z in 𝓝 (0 : ℂ), χ z = 0) (k : ℕ) :
    Continuous (planeZeroExtension (fun z => χ z * angularPhase z ^ k)) := by
  apply continuous_planeZeroExtension (contDiff_cutoff_angular_power hχ hzero k).continuous
  exact hcomp.mul_right

theorem contDiff_cutoff_angular_inv {χ : ℂ → ℂ} {n : WithTop ℕ∞}
    (hχ : ContDiff ℝ n χ) (hcomp : HasCompactSupport χ)
    (hzero : ∀ᶠ z in 𝓝 (0 : ℂ), χ z = 0) (k : ℕ) :
    ContDiff ℝ n (fun z : ℂ => χ z⁻¹ * angularPhase z⁻¹ ^ k) := by
  apply contDiff_comp_inv_of_compactSupport (contDiff_cutoff_angular_power hχ hzero k)
    hcomp.mul_right
  simp [hzero.self_of_nhds]

end Problem340

end

end OAI
