import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A compactly supported smooth interval cutoff with a full unit germ
at every point of a specified smaller closed interval. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma interval_interior_cutoff {a b c d : ℝ} (hac : a < c) (hdb : d < b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioo a b ∧ ∀ t ∈ Icc c d, η =ᶠ[𝓝 t] 1 := by
  let l := (a+c)/2
  let r := (d+b)/2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro t ht
    dsimp [l,r] at ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨η,hη,hc,_hval,hs,h1⟩ := CollarVelocity.compact_cutoff isCompact_Icc isOpen_Ioo hsub
  refine ⟨η,hη,hc,hs,?_⟩
  intro t ht
  have htI : t ∈ Ioo l r := by
    dsimp [l,r]
    constructor <;> linarith [ht.1,ht.2]
  filter_upwards [isOpen_Ioo.mem_nhds htI] with y hy
  exact h1 y ⟨hy.1.le,hy.2.le⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
