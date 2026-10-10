import OAI.Analysis.CircleDomains.Sobolev.FilledScalarSliceDerivative
import OAI.Analysis.CircleDomains.Modulus.VerticalCirclePayment
import OAI.Analysis.CircleDomains.Topology.VerticalFrontierCrossings

namespace OAI

/-! The second ordinary partial of the actual filled scalar is also its
line derivative almost everywhere, including the clipping levels. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem hasDerivAt_verticalLine (x y : ℝ) : HasDerivAt (verticalLine x) Complex.I y := by
  exact Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel.HoleFilling
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
  {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 theorem vertical_derivative_ae :
    ∀ᵐ z ∂(volume : Measure ℂ),
      deriv (F.filled ∘ verticalLine z.re) z.im = fderiv ℝ F.filled z Complex.I := by
  classical
  let : Fintype (R.model.stages n).indices := (R.model.stages n).finite_indices.fintype
  have hs : ∀ᵐ z ∂(volume : Measure ℂ), ∀ s, z ∉ sphere (F.center s) (F.radius s) := by
    apply ae_all_iff.mpr
    intro s
    exact compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (F.center s) (F.radius s))
  have hU := (R.model.stages n).circle_domain.1.preimage OnePoint.continuous_coe
  filter_upwards [hs] with z hz
  have hez : verticalLine z.re z.im = z := by apply Complex.ext <;> rfl
  by_cases hmem : z ∈ ((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain
  · have he : F.filled =ᶠ[𝓝 z] clipScalar ∘ R.transferred i n := by
      filter_upwards [hU.mem_nhds hmem] with w hw
      exact F.filled_on_domain hw
    have hd := ((R.transferred_contDiffOn i n).contDiffAt (hU.mem_nhds hmem)).differentiableAt
      (by simp)
    apply deriv_eq_fderiv_of_eventuallyEq_clip (by simpa only [hez] using he)
      (by simpa only [hez] using hd) (hasDerivAt_verticalLine z.re z.im)
  · have hout : z ∈ ⋃ s, closedBall (F.center s) (F.radius s) := by
      rw [F.complement] at hmem
      exact not_not.mp hmem
    obtain ⟨s, hsz⟩ := mem_iUnion.mp hout
    have hball : z ∈ ball (F.center s) (F.radius s) :=
      lt_of_le_of_ne hsz (fun he => hz s he)
    have he : F.filled =ᶠ[𝓝 z] fun _ => clipScalar (F.value s) := by
      filter_upwards [isOpen_ball.mem_nhds hball] with w hw
      exact F.filled_on_hole s (ball_subset_closedBall hw)
    have hc : (F.filled ∘ verticalLine z.re) =ᶠ[𝓝 z.im] fun _ => clipScalar (F.value s) := by
      exact he.comp_tendsto (by
        have hh : Tendsto (verticalLine z.re) (𝓝 z.im)
            (𝓝 (verticalLine z.re z.im)) := (continuous_verticalLine z.re).continuousAt.tendsto
        rw [hez] at hh
        exact hh)
    rw [hc.deriv_eq, deriv_const, F.filled_fderiv_on_ball s hball, zero_apply]

end RetainedRealCircleModel.HoleFilling
end CircleDomainRigidity

end

end OAI
