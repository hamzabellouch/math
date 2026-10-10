import OAI.Geometry.SurfaceImmersion.Whitney.SourceMapRepresentative

namespace OAI

/-! The coordinate representative has exactly the original map's axis velocity,
including both endpoints of the compact arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coordinate_axis_derivative (P : SmoothCompactArc planeModel M)
    (c : OpenPartialHomeomorph M Base) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f) {φ : Base → V}
    (hφ : ContDiff ℝ ∞ φ) {U : Set Base} (hEq : EqOn φ (f ∘ c.symm) U)
    (haxis : ∀ t ∈ Icc P.start P.finish,
      P.curve t ∈ c.source ∧ c (P.curve t) = ![0,t])
    (hUaxis : ∀ t ∈ Icc P.start P.finish, (![0,t] : Base) ∈ U)
    {t : ℝ} (ht : t ∈ Icc P.start P.finish) :
    fderiv ℝ φ (![0,t] : Base) (![0,1] : Base) = deriv (f ∘ P.curve) t := by
  have heq : EqOn (φ ∘ crosscapAxis) (f ∘ P.curve) (Icc P.start P.finish) := by
    intro s hs
    rw [Function.comp_apply,crosscapAxis_apply,hEq (hUaxis s hs)]
    change f (c.symm (![0,s] : Base)) = f (P.curve s)
    rw [← (haxis s hs).2,c.left_inv (haxis s hs).1]
  have hD := ((hφ.differentiable (by simp) (crosscapAxis t)).hasFDerivAt).comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hD' := hD.hasDerivWithinAt.congr_of_mem (fun s hs => (heq hs).symm) ht
  have hfD := ((hf.contMDiffAt.comp t
    (P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht)))).contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hd := ((uniqueDiffOn_Icc P.start_lt_finish) t ht).eq_deriv (Icc P.start P.finish)
    hfD.hasDerivWithinAt hD'
  simpa only [crosscapAxis_apply] using hd.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
