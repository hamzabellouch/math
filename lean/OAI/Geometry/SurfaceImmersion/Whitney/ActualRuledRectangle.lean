import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceRuledInterior
import OAI.Geometry.SurfaceImmersion.Geometry.CompactAxisGermEquality

namespace OAI

/-! A single explicit rectangular ruled region in the supported surface
replacement, with retained actual coordinate and crosscap jets. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

structure ActualRuledRectangle (S : CrosscapCoordinateStrip A) (c d : ℝ) where
  replacement : M → ProjectionTarget 3
  model : Base → ProjectionTarget 3
  support : Set M
  radius : ℝ
  radius_pos : 0 < radius
  smooth : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ replacement
  model_smooth : ContDiff ℝ ∞ model
  support_compact : IsCompact support
  support_source : support ⊆ S.chart.source
  exterior : ∀ x ∉ support, replacement =ᶠ[𝓝 x] f
  left_germ : replacement =ᶠ[𝓝 p] f
  right_germ : replacement =ᶠ[𝓝 q] f
  model_eq : EqOn model (replacement ∘ S.chart.symm) S.domain
  regular_iff : ∀ x, Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) replacement x) ↔
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)
  axis_jets : ∀ t, model (crosscapAxis t) = S.model (crosscapAxis t) ∧
    fderiv ℝ model (crosscapAxis t) = fderiv ℝ S.model (crosscapAxis t) ∧
    axisDirectionJet model (crosscapAxis t) = axisDirectionJet S.model (crosscapAxis t)
  ruled_rectangle : ∀ x ∈ Icc (-radius) radius,
    ∀ t ∈ Icc (c-radius) (d+radius), (![x,t] : Base) ∈ S.domain ∧
      model ![x,t] = transverseRuling S.model ![x,t]

theorem CrosscapCoordinateStrip.exists_actual_ruled_rectangle (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {c d : ℝ} (hac : A.arc.start < c) (hcd : c ≤ d) (hdb : d < A.arc.finish) :
    Nonempty (ActualRuledRectangle S c d) := by
  obtain ⟨g,K,G,hg,hK,hKS,hG,hmodel,hjets,hreg,hout,hl,hr,hinner⟩ :=
    S.surface_ruled_interior hf hac hdb
  have haxis : ∀ t ∈ Icc c d, crosscapAxis t ∈ S.domain := by
    intro t ht
    rw [crosscapAxis_apply]
    apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
    constructor <;> linarith [ht.1,ht.2,S.width_pos]
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_germ_equality hcd S.domain_open haxis
    (fun t ht => (hinner t ht).1)
  exact ⟨⟨g,G,K,δ,hδ,hg,hG,hK,hKS,hout,hl,hr,hmodel,hreg,hjets,hrect⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
