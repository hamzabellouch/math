import Mathlib
import OAI.Geometry.Cannon.Energy.SquareMap

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
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonCharts

lemma squareMap_range : range squareMap = Icc (1 : ℝ) 2 ×ˢ Icc (-6 : ℝ) 6 := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    change 1+(w.1:ℝ) ∈ Icc 1 2 ∧ 12*(w.2:ℝ)-6 ∈ Icc (-6) 6
    constructor <;> constructor <;> linarith [w.1.property.1,w.1.property.2,w.2.property.1,w.2.property.2]
  · rintro ⟨hx,hy⟩
    let u : unitInterval := ⟨z.1-1,by constructor <;> linarith [hx.1,hx.2]⟩
    let v : unitInterval := ⟨(z.2+6)/12,by constructor <;> linarith [hy.1,hy.2]⟩
    refine ⟨(u,v),?_⟩
    dsimp [squareMap,u,v]
    ext <;> dsimp <;> ring

lemma squareMap_interior {z : CannonGrid.Square}
    (hx : (z.1:ℝ) ∈ Ioo (0:ℝ) 1) (hy : (z.2:ℝ) ∈ Ioo (0:ℝ) 1) :
    squareMap z ∈ interior (range squareMap) := by
  rw [squareMap_range, interior_prod_eq, interior_Icc, interior_Icc]
  change 1+(z.1:ℝ) ∈ Ioo 1 2 ∧ 12*(z.2:ℝ)-6 ∈ Ioo (-6) 6
  constructor <;> constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

lemma chart_square_interior {X : Type*} [TopologicalSpace X] (e : Plane → X)
    (he : IsOpenEmbedding e) {z : CannonGrid.Square}
    (hx : (z.1:ℝ) ∈ Ioo (0:ℝ) 1) (hy : (z.2:ℝ) ∈ Ioo (0:ℝ) 1) :
    e (squareMap z) ∈ interior (range (e ∘ squareMap)) := by
  apply mem_interior.mpr
  refine ⟨e '' interior (range squareMap),?_,he.isOpenMap _ isOpen_interior,?_⟩
  · rintro y ⟨w,hw,rfl⟩
    obtain ⟨v,rfl⟩ := interior_subset hw
    exact ⟨v,rfl⟩
  · exact mem_image_of_mem e (squareMap_interior hx hy)

end CannonCharts

open Set MeasureTheory
open scoped NNReal ENNReal

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
