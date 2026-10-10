import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapAxisImageVelocity

namespace OAI

/-! The derivative at an actual crosscap has rank at least one. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {f : M → ProjectionTarget 3} {p : M}

lemma SurfaceCrosscapCoordinates.derivative_ne_zero (c : SurfaceCrosscapCoordinates f p)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p ≠ 0 := by
  intro hzero
  have h0 : (0:Base) ∈ c.source.target := by
    rw [← c.source_center]
    exact c.source.map_source c.source_mem
  have hinv : c.source.symm 0 = p := by
    rw [← c.source_center,c.source.left_inv c.source_mem]
  have hstd0 : standardCrosscap (0:Base) = 0 := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  have heq : f ∘ c.source.symm =ᶠ[𝓝 (0:Base)] c.target ∘ standardCrosscap := by
    filter_upwards [c.source.open_target.mem_nhds h0] with x hx
    have h := c.model_eq (c.source.symm x) (c.source.map_target hx)
    rwa [c.source.right_inv hx] at h
  have hcomp0 : fderiv ℝ (f ∘ c.source.symm) 0 = 0 := by
    rw [← mfderiv_eq_fderiv,mfderiv_comp 0 (hf.mdifferentiable (by simp) _)
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds h0)).mdifferentiableAt (by simp)),
      ]
    have hz : mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (c.source.symm 0) = 0 :=
      hinv.symm ▸ hzero
    rw [hz]
    exact ContinuousLinearMap.zero_comp _
  have htD : c.target.MDifferentiable 𝓘(ℝ,Base × ℝ) 𝓘(ℝ,ProjectionTarget 3) :=
    ⟨c.target_smooth.contMDiff.contMDiffOn.mdifferentiableOn (by simp),
      c.target_inverse_smooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htI : Function.Injective (fderiv ℝ c.target 0) := by
    rw [← mfderiv_eq_fderiv]
    exact htD.mfderiv_injective c.target_mem
  have hv := congrArg (fun L : Base →L[ℝ] ProjectionTarget 3 => L (![1,0] : Base))
    (heq.fderiv_eq.symm.trans hcomp0)
  rw [fderiv_comp 0 (c.target_smooth.differentiable (by simp) _)
    (standardCrosscap_hasFDerivAt 0).differentiableAt,
    (standardCrosscap_hasFDerivAt 0).fderiv,hstd0] at hv
  have hval : standardCrosscapDerivative 0 (![1,0] : Base) = (0,1) := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscapDerivative]
    · simp [standardCrosscapDerivative]
  change fderiv ℝ c.target 0 (standardCrosscapDerivative 0 (![1,0] : Base)) = 0 at hv
  rw [hval] at hv
  have hh := htI (hv.trans (map_zero _).symm)
  have hs := congrArg Prod.snd hh
  norm_num at hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
