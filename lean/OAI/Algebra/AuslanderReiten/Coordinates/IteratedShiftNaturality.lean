import OAI.Algebra.AuslanderReiten.Complete.CompleteShift

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit

universe v u
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n + 1))⟦(1 : ℤ)⟧)

def iteratedShiftIso : ∀ n : ℕ, Y 0 ≅ (Y n)⟦(n : ℤ)⟧
  | 0 => (CategoryTheory.shiftFunctorZero C ℤ).symm.app (Y 0)
  | n + 1 => iteratedShiftIso n ≪≫
      (CategoryTheory.shiftFunctor C (n : ℤ)).mapIso (s n) ≪≫
      (CategoryTheory.shiftFunctorAdd' C (1 : ℤ) (n : ℤ)
        ((n + 1 : ℕ) : ℤ) (by omega)).symm.app (Y (n + 1))

omit [HasShift C ℤ] in
private theorem compose_squares
    {A A' B B' D D' : C} {f : A ⟶ A'} {g : B ⟶ B'} {h : D ⟶ D'}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ D} {b' : B' ⟶ D'}
    (h₁ : f ≫ a' = a ≫ g) (h₂ : g ≫ b' = b ≫ h) :
    f ≫ (a' ≫ b') = (a ≫ b) ≫ h := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable {Y s} {Z : ℕ → C} (t : ∀ n, Z n ≅ (Z (n + 1))⟦(1 : ℤ)⟧)
variable (f : ∀ n, Y n ⟶ Z n)

theorem iteratedShiftIso_natural
    (hs : ∀ n, f n ≫ (t n).hom = (s n).hom ≫
      (CategoryTheory.shiftFunctor C (1 : ℤ)).map (f (n + 1))) (n : ℕ) :
    f 0 ≫ (iteratedShiftIso Z t n).hom =
      (iteratedShiftIso Y s n).hom ≫ (CategoryTheory.shiftFunctor C (n : ℤ)).map (f n) := by
  induction n with
  | zero => exact (CategoryTheory.shiftFunctorZero C ℤ).inv.naturality (f 0)
  | succ n ih =>
    let F := CategoryTheory.shiftFunctor C (n : ℤ)
    let A := CategoryTheory.shiftFunctorAdd' C (1 : ℤ) (n : ℤ)
      ((n + 1 : ℕ) : ℤ) (by omega)
    have h₂ : F.map (f n) ≫ F.map (t n).hom =
        F.map (s n).hom ≫ F.map ((CategoryTheory.shiftFunctor C (1 : ℤ)).map (f (n + 1))) := by
      rw [← F.map_comp, hs n, F.map_comp]
    have h₃ : F.map ((CategoryTheory.shiftFunctor C (1 : ℤ)).map (f (n + 1))) ≫
        A.inv.app (Z (n + 1)) = A.inv.app (Y (n + 1)) ≫
          (CategoryTheory.shiftFunctor C ((n + 1 : ℕ) : ℤ)).map (f (n + 1)) :=
      A.inv.naturality (f (n + 1))
    simpa only [iteratedShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
      Iso.symm_hom, F, A, Category.assoc] using compose_squares (compose_squares ih h₂) h₃

end ArExplicit

end

end OAI
