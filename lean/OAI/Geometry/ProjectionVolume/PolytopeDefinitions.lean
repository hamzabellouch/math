import OAI.Geometry.ProjectionVolume.Basic

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section

namespace Paper092

structure HPolytope (d : ℕ) (ι : Type uι) [Fintype ι] where
  normal : ι → Euclidean d
  offset : ι → ℝ
  normal_unit : ∀ i, ‖normal i‖ = 1
  compact : IsCompact {x : Euclidean d | ∀ i, ⟪normal i, x⟫ ≤ offset i}
  strict_feasible : ∃ x : Euclidean d, ∀ i, ⟪normal i, x⟫ < offset i
  distinct : Function.Injective (fun i => (normal i, offset i))

namespace HPolytope

def body {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) : Set (Euclidean d) :=
  {x | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i}

def face {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) (i : ι) :
    Set (Euclidean d) :=
  {x | x ∈ P.body ∧ ⟪P.normal i, x⟫ = P.offset i}

def faceArea {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) (i : ι) : ℝ :=
  (μHE[d - 1] (P.face i)).toReal

def facetZonotope {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι) :
    Set (Euclidean d) :=
  ∑ i, segment ℝ (-(P.faceArea i / 2) • P.normal i) ((P.faceArea i / 2) • P.normal i)

end HPolytope
end Paper092

end

end OAI
