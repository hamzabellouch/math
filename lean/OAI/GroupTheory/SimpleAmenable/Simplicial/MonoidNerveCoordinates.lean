import Mathlib

namespace OAI

section
open CategoryTheory Simplicial SimplicialObject Opposite
namespace MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] {n:ℕ}
abbrev Simplex (P:Type) [CommMonoid P] (n:ℕ) := ComposableArrows (SingleObj P)ᵒᵖ n
def labels (s:Simplex P n) : Fin n→P := fun i=>(s.map (homOfLE (Fin.castSucc_le_succ i))).unop
noncomputable def ofLabels (x:Fin n→P) : Simplex P n :=
  ComposableArrows.mkOfObjOfMapSucc (fun _=>op (SingleObj.star P)) (fun i=>Quiver.Hom.op (x i:SingleObj.star P⟶SingleObj.star P))
lemma eqToHom_val {x y:(SingleObj P)ᵒᵖ} (h:x=y) : (eqToHom h).unop=(1:P) := by subst y; rfl
@[simp] lemma labels_ofLabels (x:Fin n→P) : labels (ofLabels x)=x := by
  funext i
  exact congrArg Quiver.Hom.unop (ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i.val i.isLt)
@[simp] lemma ofLabels_labels (s:Simplex P n) : ofLabels (labels s)=s := by
  apply ComposableArrows.ext (fun _=>Subsingleton.elim _ _)
  intro i hi
  apply Quiver.Hom.unop_inj
  simp only [unop_comp,eqToHom_val,SingleObj.comp_as_mul,one_mul,mul_one]
  exact congrArg Quiver.Hom.unop (ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi)
noncomputable def equiv (P:Type) [CommMonoid P] (n:ℕ) : Simplex P n ≃ (Fin n→P) where
  toFun := labels
  invFun := ofLabels
  left_inv := ofLabels_labels
  right_inv := labels_ofLabels
lemma labels_zero_face (s:Simplex P (n+1)) :
    labels ((nerve _).δ (0:Fin (n+2)) s)=Fin.tail (labels s) := by funext i; rfl
lemma map_congr (s:Simplex P n) {i j i' j':Fin (n+1)} (hi:i=i') (hj:j=j')
    (f:i⟶j) (g:i'⟶j') : (s.map f).unop=(s.map g).unop := by
  subst i'; subst j'
  congr 2
  exact Subsingleton.elim _ _
lemma labels_last_face (s:Simplex P (n+1)) :
    labels ((nerve _).δ (Fin.last (n+1)) s)=Fin.init (labels s) := by
  funext i
  change (s.map (homOfLE (show (Fin.last (n+1)).succAbove i.castSucc ≤
      (Fin.last (n+1)).succAbove i.succ from by simpa using Fin.castSucc_le_succ i.castSucc))).unop =
      (s.map (homOfLE (Fin.castSucc_le_succ i.castSucc))).unop
  apply map_congr s <;> simp
end MonoidNerveCoordinates

end

end OAI
