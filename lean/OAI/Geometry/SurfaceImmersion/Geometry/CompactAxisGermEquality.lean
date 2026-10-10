import OAI.Geometry.SurfaceImmersion.Geometry.CompactAxisRectangle

namespace OAI

/-! Pointwise germs along a compact axis interval give one actual closed
 rectangle of equality, contained in the specified open domain. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*}

theorem compact_axis_germ_equality {f g : Base → V} {a b : ℝ} (hab : a ≤ b)
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc a b, crosscapAxis t ∈ U)
    (he : ∀ t ∈ Icc a b, f =ᶠ[𝓝 (crosscapAxis t)] g) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (a-δ) (b+δ),
      (![x,t] : Base) ∈ U ∧ f ![x,t] = g ![x,t] := by
  let W := U ∩ interior {x | f x = g x}
  have hW : IsOpen W := hU.inter isOpen_interior
  have hAW : ∀ t ∈ Icc a b, (![0,t] : Base) ∈ W := by
    intro t ht
    have hm : crosscapAxis t ∈ interior {x | f x = g x} :=
      mem_interior_iff_mem_nhds.mpr (he t ht)
    simpa only [W,mem_inter_iff,crosscapAxis_apply] using And.intro (haxis t ht) hm
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle hab hW hAW
  refine ⟨δ,hδ,?_⟩
  intro x hx t ht
  have hm := hrect x hx t ht
  exact ⟨hm.1,(interior_subset hm.2 : (![x,t] : Base) ∈ {y | f y = g y})⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
