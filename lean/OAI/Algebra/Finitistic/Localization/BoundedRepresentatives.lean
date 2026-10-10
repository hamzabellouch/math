import OAI.Algebra.Finitistic.Localization.BoundedHomotopy

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BoundedHomotopy
variable (C : Type*) [Category* C] [Preadditive C]

/-- An actual bounded representative of each homotopy-category object. -/
def representative (X : K C) : Complex C :=
  ⟨X.obj.as, (bounded_quotient_obj_iff _ _).mp X.property⟩

@[simp] theorem quotient_representative (X : K C) :
    (quotient C).obj (representative C X) = X := by
  cases X
  rfl

variable {C}
/-- A bounded chain-map representative of a homotopy-category morphism. -/
def representativeMap {X Y : K C} (f : X ⟶ Y) :
    representative C X ⟶ representative C Y :=
  ObjectProperty.homMk ((HomotopyCategory.quotient C (.up ℤ)).preimage f.hom)

@[simp] theorem quotient_representativeMap {X Y : K C} (f : X ⟶ Y) :
    (HomotopyCategory.quotient C (.up ℤ)).map (representativeMap f).hom = f.hom :=
  (HomotopyCategory.quotient C (.up ℤ)).map_preimage _

/-- Zero in K means a genuine right-linear null-homotopy of the chain representative. -/
def nullHomotopy {X Y : Complex C} (f : X ⟶ Y) (hf : (quotient C).map f = 0) :
    Homotopy f.hom 0 :=
  HomotopyCategory.homotopyOfEq _ _ (by
    have h := congrArg (fun g : (quotient C).obj X ⟶ (quotient C).obj Y =>
      (bounded C).ι.map g) hf
    rw [Functor.map_zero] at h
    exact h)

end LittleFinitistic.BoundedHomotopy

end

end OAI
