import OAI.Geometry.SurfaceImmersion.Geometry.CompactFixedJet

namespace OAI

/-! The regular locus common to a compact parameter family is open. -/
noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma compact_family_regular_locus_open {K : Set ℝ} (hK : IsCompact K)
    (D : ℝ → Base → Base →L[ℝ] ProjectionTarget 3)
    (hD : Continuous (fun z : ℝ × Base => D z.1 z.2)) :
    IsOpen {x | ∀ t ∈ K, Function.Injective (D t x)} := by
  let O := {z : ℝ × Base | Function.Injective (D z.1 z.2)}
  have hO : IsOpen O := ContinuousLinearMap.isOpen_injective.preimage hD
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hsub : K ×ˢ {x} ⊆ O := by
    rintro ⟨t,y⟩ ⟨ht,hy⟩
    have he : y = x := hy
    subst y
    exact hx t ht
  obtain ⟨V,U,hV,hU,hKV,hxU,hVU⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  apply Filter.mem_of_superset (hU.mem_nhds (hxU (by simp)))
  intro y hy
  change ∀ t ∈ K, Function.Injective (D t y)
  intro t ht
  exact hVU (show (t,y) ∈ V ×ˢ U from ⟨hKV ht,hy⟩)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
