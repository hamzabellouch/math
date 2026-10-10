import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolygonModel
import OAI.Geometry.HyperbolicGroups.CyclicTriangleCochains

namespace OAI

section


/-! Explicit cyclic antiderivatives for the literal threefold-subdivided
polygon corners. This retains the actual constructor `Position`. -/
noncomputable section
namespace HyperbolicObstruction.FinitePolygonModel.Data
open CyclicTriangleBoundary
variable {V E C B : Type*} [AddCommGroup B]
  (P : Data V E C)

def cornerPrimitive (f : P.Position → B) (q : P.Position) : B :=
  cyclePrimitive (fun i => ∑ j : Fin 3, f ⟨q.1,(i,j)⟩) q.2.1 -
    ∑ j ∈ Finset.Iio q.2.2, f ⟨q.1,(q.2.1,j)⟩

lemma cornerPrimitive_difference (f : P.Position → B)
    (hf : ∀ c, ∑ i : Fin (P.size c), ∑ j : Fin 3, f ⟨c,(i,j)⟩ = 0)
    (q : P.Position) : P.cornerPrimitive f q - P.cornerPrimitive f (P.next q) = f q := by
  have h0 : Finset.Iio (0 : Fin 3) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0,1} := by decide
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · simp [cornerPrimitive,next,Fin.sum_univ_succ,h0,h1]
  · simp [cornerPrimitive,next,Fin.sum_univ_succ,h1,h2]
  · have hh := cyclePrimitive_difference (fun i => ∑ j : Fin 3, f ⟨c,(i,j)⟩) (hf c) i
    simp only [cornerPrimitive]
    change (cyclePrimitive _ i - ∑ j ∈ Finset.Iio (2 : Fin 3), f ⟨c,(i,j)⟩) -
      (cyclePrimitive _ (finRotate (P.size c) i) - ∑ j ∈ Finset.Iio (0 : Fin 3), f ⟨c,(finRotate (P.size c) i,j)⟩) = f ⟨c,(i,2)⟩
    rw [h2,h0,Finset.sum_empty,sub_zero,Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
    calc _ = (cyclePrimitive (fun i => ∑ j : Fin 3, f ⟨c,(i,j)⟩) i -
        cyclePrimitive (fun i => ∑ j : Fin 3, f ⟨c,(i,j)⟩) (finRotate (P.size c) i)) -
        (f ⟨c,(i,0)⟩ + f ⟨c,(i,1)⟩) := by abel
      _ = _ := by
        rw [hh]
        simp only [Fin.sum_univ_three]
        abel

end HyperbolicObstruction.FinitePolygonModel.Data
end
end

section

end

end OAI
