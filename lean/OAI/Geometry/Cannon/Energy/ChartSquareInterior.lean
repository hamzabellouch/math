import Mathlib
import OAI.Geometry.Cannon.Energy.SquareMapRange

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology Metric unitInterval

namespace CannonCharts

lemma chart_square_interior_eq {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) :
    interior (range (e ∘ squareMap)) = e '' (Ioo (1:ℝ) 2 ×ˢ Ioo (-6:ℝ) 6) := by
  have hpre : e ⁻¹' range (e ∘ squareMap) = range squareMap := by
    ext z
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨w,he.injective hw⟩
    · rintro ⟨w,rfl⟩
      exact mem_range_self w
  have hi : e ⁻¹' interior (range (e ∘ squareMap)) = Ioo (1:ℝ) 2 ×ˢ Ioo (-6:ℝ) 6 := by
    rw [he.isOpenMap.preimage_interior_eq_interior_preimage he.continuous,hpre,
      squareMap_range,interior_prod_eq,interior_Icc,interior_Icc]
  apply Subset.antisymm
  · intro z hz
    obtain ⟨w,rfl⟩ := interior_subset hz
    exact ⟨squareMap w,hi ▸ hz,rfl⟩
  · rintro z ⟨w,hw,rfl⟩
    change w ∈ e ⁻¹' interior (range (e ∘ squareMap))
    rwa [hi]

lemma chart_square_pathConnected {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) : IsPathConnected (interior (range (e ∘ squareMap))) := by
  rw [chart_square_interior_eq e he]
  exact ((convex_Ioo (𝕜 := ℝ) (1:ℝ) 2).isPathConnected
    ⟨3/2,by norm_num⟩ |>.prod
    ((convex_Ioo (𝕜 := ℝ) (-6:ℝ) 6).isPathConnected
    ⟨0,by norm_num⟩)).image he.continuous

lemma chart_origin_outside_square {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) : e (0,0) ∉ interior (range (e ∘ squareMap)) := by
  intro hz
  rw [chart_square_interior_eq e he] at hz
  obtain ⟨w,hw,hwe⟩ := hz
  have hwz : w = (0,0) := he.injective hwe
  subst w
  norm_num at hw

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
