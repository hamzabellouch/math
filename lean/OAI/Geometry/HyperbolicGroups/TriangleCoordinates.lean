import Mathlib
import OAI.Geometry.HyperbolicGroups.VoltageTriangles

namespace OAI

/-! Actual simplex coordinates and exact boundary decomposition. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

omit [Fintype V] [DecidableEq V] in
lemma three_injective {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a,b,c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

def triangleCoordinates {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) : Triangle ≃ₜ closedFace (K := K) {a,b,c} :=
  (simplexCoordinates he).trans
    ((Homeomorph.setCongr (congrArg simplex (triangle_image a b c))).trans
      (closedSimplexHomeomorph K h))

lemma triangleCoordinates_apply {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) (z : Triangle) :
    triangleCoordinates h he z = trianglePoint h z := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

lemma trianglePoint_surjective {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) : Function.Surjective (trianglePoint h) := by
  intro x
  obtain ⟨z,hz⟩ := (triangleCoordinates h he).surjective x
  exact ⟨z,(triangleCoordinates_apply h he z).symm.trans hz⟩

lemma trianglePoint_coordinate {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) (z : Triangle) (i : Fin 3) :
    (trianglePoint h z).val.val (![a,b,c] i) = z.val i :=
  barycentric_at he z i

end HyperbolicObstruction.FinitePolyhedron.Voltage

end

end OAI
