import OAI.Analysis.CircleDomains.Sobolev.ClippedDirectionalDerivative
import OAI.Analysis.CircleDomains.Sobolev.FilledScalarGlobalEnergy

namespace OAI

/-! Actual line derivatives of the finite filling agree almost everywhere
with its ordinary planar partials. Circular boundaries are the only exclusions. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem transferred_contDiffOn (i : Fin m) (n : ℕ) :
    ContDiffOn ℝ ∞ (R.transferred i n) (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  rw [transferred, transported_sphereRealFunction_eq]
  exact ((R.model.stages n).transported_smooth (prefixIndex (R.index i) n)).comp
    Complex.equivRealProdCLM.contDiff.contDiffOn (fun z hz => by
      simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz)

namespace HoleFilling
variable {R} {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 theorem horizontal_derivative_ae :
    ∀ᵐ z ∂(volume : Measure ℂ),
      deriv (F.filled ∘ horizontalLine z.im) z.re = fderiv ℝ F.filled z 1 := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ s, z ∉ sphere (F.center s) (F.radius s) := by
    apply ae_all_iff.mpr
    intro s
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (F.center s) (F.radius s))
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  filter_upwards [hs] with z hz
  have hez : horizontalLine z.im z.re = z := by apply Complex.ext <;> rfl
  by_cases hmem : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
  · have he : F.filled =ᶠ[𝓝 z] clipScalar ∘ R.transferred i n := by
      filter_upwards [hU.mem_nhds hmem] with w hw
      exact F.filled_on_domain hw
    have hd := ((R.transferred_contDiffOn i n).contDiffAt (hU.mem_nhds hmem)).differentiableAt
      (by simp)
    apply deriv_eq_fderiv_of_eventuallyEq_clip (by simpa only [hez] using he)
      (by simpa only [hez] using hd) (hasDerivAt_horizontalLine z.re z.im)
  · have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      rw [F.complement] at hmem
      exact not_not.mp hmem
    obtain ⟨s, hsz⟩ := mem_iUnion.mp hout
    have hball : z ∈ ball (F.center s) (F.radius s) :=
      lt_of_le_of_ne hsz (fun he => hz s he)
    have he : F.filled =ᶠ[𝓝 z] fun _ => clipScalar (F.value s) := by
      filter_upwards [isOpen_ball.mem_nhds hball] with w hw
      exact F.filled_on_hole s (ball_subset_closedBall hw)
    have hc : (F.filled ∘ horizontalLine z.im) =ᶠ[𝓝 z.re] fun _ => clipScalar (F.value s) := by
      simpa only [comp_def, hez] using he.comp_tendsto
        (show Tendsto (horizontalLine z.im) (𝓝 z.re) (𝓝 z) by
          have hh : Tendsto (horizontalLine z.im) (𝓝 z.re)
              (𝓝 (horizontalLine z.im z.re)) := (continuous_horizontalLine z.im).continuousAt.tendsto
          rw [hez] at hh
          exact hh)
    rw [hc.deriv_eq, deriv_const, F.filled_fderiv_on_ball s hball, zero_apply]

end HoleFilling
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
