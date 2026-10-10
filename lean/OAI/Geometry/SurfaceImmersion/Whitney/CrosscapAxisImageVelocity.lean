import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapConnectingArc

namespace OAI

/-! Exact endpoint axis germs force zero image velocity at each crosscap. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {f : M → ProjectionTarget 3} {p : M}

lemma crosscap_axis_image_velocity (c : SurfaceCrosscapCoordinates f p)
    {γ : ℝ → M} {a : ℝ} (e : ℝ → ℝ) (he : ContDiff ℝ ∞ e) (he0 : e a = 0)
    (hγ : γ =ᶠ[𝓝 a] c.axisCurve ∘ e) : deriv (f ∘ γ) a = 0 := by
  have heD := (he.differentiable (by simp) a).hasDerivAt
  have haD := crosscapAxis.hasFDerivAt.comp_hasDerivAt a heD
  have hstd := (standardCrosscap_hasFDerivAt (crosscapAxis (e a))).comp_hasDerivAt a haD
  have hz : standardCrosscapDerivative (crosscapAxis (e a))
      (crosscapAxis (deriv e a)) = 0 := by
    rw [he0,map_zero]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscapDerivative,crosscapAxis_apply]
    · simp [standardCrosscapDerivative,crosscapAxis_apply]
  rw [hz] at hstd
  have htar := (c.target_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt a hstd
  have h0 : (0:Base) ∈ c.source.target := by
    rw [← c.source_center]
    exact c.source.map_source c.source_mem
  have hnear : ∀ᶠ t in 𝓝 a, crosscapAxis (e t) ∈ c.source.target := by
    apply (c.source.open_target.preimage (crosscapAxis.continuous.comp he.continuous)).mem_nhds
    change crosscapAxis (e a) ∈ c.source.target
    rw [he0,map_zero]
    exact h0
  have hEq : f ∘ γ =ᶠ[𝓝 a] c.target ∘ (standardCrosscap ∘ (crosscapAxis ∘ e)) := by
    filter_upwards [hγ,hnear] with t ht htS
    have hm := c.model_eq (c.source.symm (crosscapAxis (e t))) (c.source.map_target htS)
    rw [c.source.right_inv htS] at hm
    simpa only [Function.comp_apply,ht,SurfaceCrosscapCoordinates.axisCurve] using hm
  rw [hEq.deriv_eq]
  exact htar.deriv.trans (map_zero _)

lemma CrosscapConnectingArc.endpoint_image_velocity [T2Space M]
    {q : M} (A : CrosscapConnectingArc f p q) :
    deriv (f ∘ A.arc.curve) A.arc.start = 0 ∧
      deriv (f ∘ A.arc.curve) A.arc.finish = 0 :=
  ⟨crosscap_axis_image_velocity A.left A.leftParameter A.left_smooth A.left_zero A.left_germ,
    crosscap_axis_image_velocity A.right A.rightParameter A.right_smooth A.right_zero A.right_germ⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
