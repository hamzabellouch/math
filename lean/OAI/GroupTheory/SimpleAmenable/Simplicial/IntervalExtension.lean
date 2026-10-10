import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalBar

namespace OAI

section

section

open CategoryTheory MonoidalCategory
universe u v w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {I : Type w} [Preorder I]

lemma cut_propagate (D E : Diagram C I) (i j k l : I)
    (hij : i≤j) (hjk : j≤k) (hkl : k≤l)
    (x : D.obj i j hij ⟶ E.obj i j hij)
    (y : D.obj j k hjk ⟶ E.obj j k hjk)
    (z : D.obj k l hkl ⟶ E.obj k l hkl)
    (xy : D.obj i k (hij.trans hjk) ⟶ E.obj i k (hij.trans hjk))
    (yz : D.obj j l (hjk.trans hkl) ⟶ E.obj j l (hjk.trans hkl))
    (xyz : D.obj i l (hij.trans (hjk.trans hkl)) ⟶ E.obj i l (hij.trans (hjk.trans hkl)))
    (hxy : (x⊗ₘy) ≫ (E.cut i j k hij hjk).hom = (D.cut i j k hij hjk).hom ≫ xy)
    (hyz : (y⊗ₘz) ≫ (E.cut j k l hjk hkl).hom = (D.cut j k l hjk hkl).hom ≫ yz)
    (hxyz : (xy⊗ₘz) ≫ (E.cut i k l (hij.trans hjk) hkl).hom =
      (D.cut i k l (hij.trans hjk) hkl).hom ≫ xyz) :
    (x⊗ₘyz) ≫ (E.cut i j l hij (hjk.trans hkl)).hom =
      (D.cut i j l hij (hjk.trans hkl)).hom ≫ xyz := by
  apply (cancel_epi ((α_ (D.obj i j hij) (D.obj j k hjk) (D.obj k l hkl)).hom ≫
      (𝟙 _ ⊗ₘ (D.cut j k l hjk hkl).hom))).mp
  calc
    _ = (α_ _ _ _).hom ≫ (x⊗ₘ((D.cut j k l hjk hkl).hom≫yz)) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by
      simp only [Category.assoc,tensorHom_comp_tensorHom_assoc,Category.id_comp]
    _ = (α_ _ _ _).hom ≫ (x⊗ₘ((y⊗ₘz)≫(E.cut j k l hjk hkl).hom)) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by rw [hyz]
    _ = (α_ _ _ _).hom ≫ (x⊗ₘ(y⊗ₘz)) ≫ (𝟙 _ ⊗ₘ (E.cut j k l hjk hkl).hom) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by
      simp only [tensorHom_comp_tensorHom_assoc,Category.comp_id]
    _ = ((x⊗ₘy)⊗ₘz) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ₘ (E.cut j k l hjk hkl).hom) ≫
        (E.cut i j l hij (hjk.trans hkl)).hom := by rw [associator_naturality_assoc]
    _ = ((x⊗ₘy)⊗ₘz) ≫ ((E.cut i j k hij hjk).hom ⊗ₘ 𝟙 _) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by
      rw [id_tensorHom,←E.associativity,tensorHom_id]
    _ = (((x⊗ₘy)≫(E.cut i j k hij hjk).hom)⊗ₘz) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by
      simp only [tensorHom_comp_tensorHom_assoc,Category.comp_id]
    _ = (((D.cut i j k hij hjk).hom≫xy)⊗ₘz) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by rw [hxy]
    _ = ((D.cut i j k hij hjk).hom⊗ₘ𝟙 _) ≫ (xy⊗ₘz) ≫
        (E.cut i k l (hij.trans hjk) hkl).hom := by
      simp only [tensorHom_comp_tensorHom_assoc,Category.id_comp]
    _ = ((D.cut i j k hij hjk).hom⊗ₘ𝟙 _) ≫ (D.cut i k l (hij.trans hjk) hkl).hom ≫ xyz := by rw [hxyz]
    _ = _ := by rw [tensorHom_id,←Category.assoc,D.associativity]; simp only [Category.assoc,id_tensorHom]

variable {n : ℕ} {D E : Diagram C (Fin (n+1))}

noncomputable def extendApp
    (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j)) :
    ∀i j (hij : i≤j), D.obj i j hij ⟶ E.obj i j hij := fun i j hij =>
  (Fin.induction
    (motive := fun j => ∀i (h : i≤j), D.obj i j h ⟶ E.obj i j h)
    (fun i hi => by
      have he : i=0 := Fin.eq_of_val_eq (by simpa using hi)
      subst i
      exact (D.unit 0).hom ≫ (E.unit 0).inv)
    (fun k prev i hi => by
      by_cases he : i=k.succ
      · subst i
        exact (D.unit k.succ).hom ≫ (E.unit k.succ).inv
      · have hik : i≤k.castSucc := by
          simp only [Fin.le_def,Fin.ext_iff,Fin.val_succ,Fin.val_castSucc] at *
          omega
        exact (D.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).inv ≫
          (prev i hik ⊗ₘ f k) ≫ (E.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom)
    j) i hij

@[simp] lemma extendApp_self (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j)) (i : Fin (n+1)) :
    extendApp f i i le_rfl = (D.unit i).hom ≫ (E.unit i).inv := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => simp [extendApp,Fin.induction_succ]

lemma extendApp_succ (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j))
    (i : Fin (n+1)) (k : Fin n) (hik : i≤k.castSucc) :
    extendApp f i k.succ (hik.trans (Fin.castSucc_le_succ k)) =
      (D.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).inv ≫
      (extendApp f i k.castSucc hik ⊗ₘ f k) ≫
        (E.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom := by
  have he : i≠k.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_succ] at hh
    have hi : i.val≤k.val := hik
    omega
  simp only [extendApp,Fin.induction_succ,dite_eq_right he]

lemma extendApp_succ_square
    (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j))
    (i : Fin (n+1)) (k : Fin n) (hik : i≤k.castSucc) :
    (extendApp f i k.castSucc hik ⊗ₘ f k) ≫
        (E.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom =
      (D.cut i k.castSucc k.succ hik (Fin.castSucc_le_succ k)).hom ≫
        extendApp f i k.succ (hik.trans (Fin.castSucc_le_succ k)) := by
  rw [extendApp_succ f i k hik]
  simp

lemma unit_left_square (D E : Diagram C I) (i j : I) (hij : i≤j)
    (f : D.obj i j hij ⟶ E.obj i j hij) :
    (((D.unit i).hom ≫ (E.unit i).inv)⊗ₘf) ≫ (E.cut i i j le_rfl hij).hom =
      (D.cut i i j le_rfl hij).hom ≫ f := by
  rw [D.left_unit,E.left_unit,tensorHom_comp_whiskerRight_assoc]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [MonoidalCategory.tensorHom_def,Category.assoc,leftUnitor_naturality]

lemma unit_right_square (D E : Diagram C I) (i j : I) (hij : i≤j)
    (f : D.obj i j hij ⟶ E.obj i j hij) :
    (f⊗ₘ((D.unit j).hom ≫ (E.unit j).inv)) ≫ (E.cut i j j hij le_rfl).hom =
      (D.cut i j j hij le_rfl).hom ≫ f := by
  rw [D.right_unit,E.right_unit,tensorHom_comp_whiskerLeft_assoc]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rw [MonoidalCategory.tensorHom_def',Category.assoc,rightUnitor_naturality]

lemma extendApp_cut
    (f : ∀j : Fin n, D.obj j.castSucc j.succ (Fin.castSucc_le_succ j) ⟶
      E.obj j.castSucc j.succ (Fin.castSucc_le_succ j)) :
    ∀k (j i : Fin (n+1)) (hij : i≤j) (hjk : j≤k),
      (extendApp f i j hij ⊗ₘ extendApp f j k hjk) ≫ (E.cut i j k hij hjk).hom =
        (D.cut i j k hij hjk).hom ≫ extendApp f i k (hij.trans hjk) := by
  apply Fin.induction
  · intro j i hij hjk
    have hj : j=0 := Fin.eq_of_val_eq (by simpa using hjk)
    subst j
    rw [extendApp_self]
    exact unit_right_square D E i 0 hij (extendApp f i 0 hij)
  · intro k ih j i hij hjk
    by_cases he : j=k.succ
    · subst j
      rw [extendApp_self]
      exact unit_right_square D E i k.succ hij (extendApp f i k.succ hij)
    · have hj : j≤k.castSucc := by
        simp only [Fin.le_def,Fin.ext_iff,Fin.val_succ,Fin.val_castSucc] at *
        omega
      exact cut_propagate D E i j k.castSucc k.succ hij hj (Fin.castSucc_le_succ k)
        (extendApp f i j hij) (extendApp f j k.castSucc hj) (f k)
        (extendApp f i k.castSucc (hij.trans hj)) (extendApp f j k.succ hjk)
        (extendApp f i k.succ (hij.trans hjk)) (ih j i hij hj)
        (extendApp_succ_square f j k hj) (extendApp_succ_square f i k (hij.trans hj))

noncomputable def extend (f : (eval n).obj D ⟶ (eval n).obj E) : D ⟶ E where
  app := extendApp f
  unit i := by rw [extendApp_self f i]; simp
  cut i j k hij hjk := extendApp_cut f k j i hij hjk

lemma extend_elementary (f : (eval n).obj D ⟶ (eval n).obj E) (i : Fin n) :
    (extend f).app i.castSucc i.succ (Fin.castSucc_le_succ i) = f i := by
  change extendApp f i.castSucc i.succ _ = f i
  apply (cancel_epi (D.cut i.castSucc i.castSucc i.succ le_rfl (Fin.castSucc_le_succ i)).hom).mp
  rw [←extendApp_succ_square f i.castSucc i le_rfl,extendApp_self f i.castSucc]
  exact unit_left_square D E i.castSucc i.succ (Fin.castSucc_le_succ i) (f i)

noncomputable instance : (eval (C:=C) n).Full where
  map_surjective f := ⟨extend f,by funext i; exact extend_elementary f i⟩

end IntervalBar.Diagram

end

end

end OAI
