import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.MonoidNerveCoordinates

namespace OAI

section
open CategoryTheory Simplicial SimplicialObject Opposite
namespace MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] {n:ℕ}
def faceLabels (k:Fin (n+2)) (x:Fin (n+1)→P) : Fin n→P := fun j=>
  if j.val+1 < k.val then x j.castSucc else
  if j.val+1 = k.val then x j.castSucc * x j.succ else x j.succ
lemma labels_face (s:Simplex P (n+1)) (k:Fin (n+2)) :
    labels ((nerve _).δ k s)=faceLabels k (labels s) := by
  funext j
  dsimp only [faceLabels]
  change (s.map (homOfLE (show k.succAbove j.castSucc ≤ k.succAbove j.succ from
    (Fin.succAboveOrderEmb k).monotone (Fin.castSucc_le_succ j)))).unop = _
  split_ifs with h h'
  · apply map_congr s
    · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val < k.val; omega)
    · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val+1 < k.val; exact h)
  · have hh : k.succAbove j.castSucc=j.castSucc.castSucc :=
      Fin.succAbove_of_castSucc_lt _ _ (by change j.val < k.val; omega)
    have hh' : k.succAbove j.succ=j.succ.succ :=
      Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ j.val+1; omega)
    rw [map_congr s hh hh' _ (homOfLE (show j.castSucc.castSucc ≤ j.succ.succ from by
      change j.val ≤ j.val+2; omega))]
    have hc:=congrArg Quiver.Hom.unop (s.map_comp
      (homOfLE (Fin.castSucc_le_succ j.castSucc))
      (homOfLE (Fin.castSucc_le_succ j.succ)))
    exact hc
  · apply map_congr s
    · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ j.val; omega)
    · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ j.val+1; omega)
lemma tail_face_val (s:Simplex P (n+1)) (k:Fin (n+2)) (hk:k≠Fin.last (n+1)) :
    (s.map (homOfLE (Fin.le_last (k.succAbove (Fin.last n))))).unop=(1:P) := by
  have h:k.succAbove (Fin.last n)=Fin.last (n+1) := by
    apply Fin.ext
    rw [Fin.succAbove_of_le_castSucc _ _ (by change k.val ≤ n; have:=k.isLt; have hn:=Fin.val_ne_of_ne hk; dsimp at hn; omega)]
    rfl
  have he:=map_congr s h rfl (homOfLE (Fin.le_last (k.succAbove (Fin.last n)))) (𝟙 _)
  rw [he,s.map_id]
  rfl
lemma tail_face_last_val (s:Simplex P (n+1)) :
    (s.map (homOfLE (Fin.le_last ((Fin.last (n+1)).succAbove (Fin.last n))))).unop=labels s (Fin.last n) := by
  apply map_congr s
  · simp
  · rfl
end MonoidNerveCoordinates

end

end OAI
