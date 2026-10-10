import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # The simplicial prism on tuples

The universal homogeneous simplex on a set has one simplex for every tuple.
Two maps of vertices are joined by the prism that uses the first map before
a chosen vertex and the second map afterwards.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped Simplicial

variable {A B : Type} {n : ℕ}

def tupleSimplicial (A : Type) : SimplicialObject (Type) where
  obj q := Fin (q.unop.len + 1) → A
  map f := ↾fun x => x ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tupleSimplicialMap (f : A → B) : tupleSimplicial A ⟶ tupleSimplicial B where
  app _ := ↾fun x => f ∘ x
  naturality _ _ _ := rfl

def tuplePrism (f g : A → B) (i : Fin (n + 1))
    (x : Fin (n + 1) → A) (k : Fin (n + 2)) : B :=
  if h : k.val ≤ i.val then f (x ⟨k.val, lt_of_le_of_lt h i.isLt⟩)
  else g (x ⟨k.val - 1, by omega⟩)

@[simp] theorem tuplePrism_zero (f g : A → B) (i : Fin (n + 1))
    (x : Fin (n + 1) → A) : tuplePrism f g i x 0 = f (x 0) := by
  simp [tuplePrism]

theorem tuplePrism_first_face (f g : A → B) (x : Fin (n + 1) → A) :
    tuplePrism f g 0 x ∘ (0 : Fin (n + 2)).succAbove = g ∘ x := by
  funext k
  simp [tuplePrism, Fin.succAbove_zero]

theorem tuplePrism_last_face (f g : A → B) (x : Fin (n + 1) → A) :
    tuplePrism f g (Fin.last n) x ∘ (Fin.last (n + 1)).succAbove = f ∘ x := by
  funext k
  simp [tuplePrism, Fin.succAbove_last, Nat.le_of_lt_succ k.isLt]

private theorem tupleSuccAbove_val {m : ℕ} (i : Fin (m + 1)) (k : Fin m) :
    (i.succAbove k).val = if k.val < i.val then k.val else k.val + 1 := by
  by_cases h : k.val < i.val
  · have h' : k.castSucc < i := h
    rw [Fin.succAbove, ite_eq_left h', ite_eq_left h]
    rfl
  · have h' : ¬k.castSucc < i := h
    rw [Fin.succAbove, ite_eq_right h', ite_eq_right h]
    rfl

private theorem tuplePredAbove_val {m : ℕ} (i : Fin m) (k : Fin (m + 1)) :
    (i.predAbove k).val = if i.val < k.val then k.val - 1 else k.val := by
  by_cases h : i.val < k.val
  · have h' : i.castSucc < k := h
    rw [Fin.predAbove, dite_eq_left h', ite_eq_left h]
    rfl
  · have h' : ¬i.castSucc < k := h
    rw [Fin.predAbove, dite_eq_right h', ite_eq_right h]
    rfl

theorem tuplePrism_face_before (f g : A → B) (i : Fin (n + 2))
    (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (x : Fin (n + 2) → A) :
    tuplePrism f g j.succ x ∘ i.castSucc.succAbove =
      tuplePrism f g j (x ∘ i.succAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tupleSuccAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.le_def, Fin.val_castSucc] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tupleSuccAbove_val]
  all_goals split_ifs <;> omega

theorem tuplePrism_face_middle (f g : A → B) (j : Fin (n + 1))
    (x : Fin (n + 2) → A) :
    tuplePrism f g j.succ x ∘ j.castSucc.succ.succAbove =
      tuplePrism f g j.castSucc x ∘ j.castSucc.succ.succAbove := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tupleSuccAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals first | rfl | omega

theorem tuplePrism_face_after (f g : A → B) (i : Fin (n + 2))
    (j : Fin (n + 1)) (hji : j.castSucc < i) (x : Fin (n + 2) → A) :
    tuplePrism f g j.castSucc x ∘ i.succ.succAbove =
      tuplePrism f g j (x ∘ i.succAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tupleSuccAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.lt_def, Fin.val_castSucc] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tupleSuccAbove_val]
  all_goals split_ifs <;> omega

theorem tuplePrism_degeneracy_before (f g : A → B) (i j : Fin (n + 1))
    (hij : i ≤ j) (x : Fin (n + 1) → A) :
    tuplePrism f g j x ∘ i.castSucc.predAbove =
      tuplePrism f g j.succ (x ∘ i.predAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tuplePredAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.le_def] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tuplePredAbove_val]
  all_goals split_ifs <;> omega

theorem tuplePrism_degeneracy_after (f g : A → B) (i j : Fin (n + 1))
    (hji : j ≤ i) (x : Fin (n + 1) → A) :
    tuplePrism f g j x ∘ i.succ.predAbove =
      tuplePrism f g j.castSucc (x ∘ i.predAbove) := by
  funext k
  simp only [tuplePrism, Function.comp_apply, tuplePredAbove_val,
    Fin.val_castSucc, Fin.val_succ]
  repeat' split
  all_goals try simp only [Fin.le_def] at *
  all_goals first | omega | (congr 2; apply Fin.ext)
  all_goals simp only [tuplePredAbove_val]
  all_goals split_ifs <;> omega

/-- The usual prism is a genuine simplicial homotopy. -/
def tupleSimplicialHomotopy (f g : A → B) :
    SimplicialObject.Homotopy (tupleSimplicialMap f) (tupleSimplicialMap g) where
  h i := ↾tuplePrism f g i
  h_zero_comp_δ_zero _ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_first_face f g x
  h_last_comp_δ_last _ := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_last_face f g x
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_face_before f g i j hij x
  h_succ_comp_δ_castSucc_succ j := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_face_middle f g j x
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_face_after f g i j hji x
  h_comp_σ_castSucc_of_le i j hij := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_degeneracy_before f g i j hij x
  h_comp_σ_succ_of_lt i j hji := by
    apply ConcreteCategory.hom_ext
    intro x
    exact tuplePrism_degeneracy_after f g i j hji x

end PolycyclicRecognition

end

end OAI
