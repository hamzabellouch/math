import OAI.Algebra.Finitistic.Bar.BarFunctor

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section

namespace DerivedBar
universe u
abbrev moduleForgetAdd (A : Type u) [Ring A] : ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} A) AddCommGrpCat
variable {A : Type u} [Ring A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
local notation "c" => ComplexShape.down ℕ

local notation "F" => moduleForgetAdd A

/-- Additive maps out of a module totalization, using its preserved coproduct.
This permits unit insertion, which need not be A-linear. -/
def totalAddDesc {n : ℕ} {Y : AddCommGrpCat.{u}}
    (f : ∀ i q (_ : i+q=n), (F).obj ((K.X i).X q) ⟶ Y) :
    (F).obj ((K.total c).X n) ⟶ Y :=
  (isColimitOfPreserves F (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π c c c) n)).desc
    { pt := Y
      ι := Discrete.natTrans (fun j => f j.as.val.1 j.as.val.2 j.as.property) }

@[reassoc (attr := simp)]
theorem ι_totalAddDesc {n : ℕ} {Y : AddCommGrpCat.{u}}
    (f : ∀ i q (_ : i+q=n), (F).obj ((K.X i).X q) ⟶ Y)
    (i q : ℕ) (h : i+q=n) :
    (F).map (K.ιTotal c i q n h) ≫ totalAddDesc K f = f i q h := by
  exact (isColimitOfPreserves F (K.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π c c c) n)).fac _ ⟨⟨⟨i,q⟩,h⟩⟩

theorem totalAdd_hom_ext {n : ℕ} {Y : AddCommGrpCat.{u}}
    {f g : (F).obj ((K.total c).X n) ⟶ Y}
    (h : ∀ i q (hi : i+q=n),
      (F).map (K.ιTotal c i q n hi) ≫ f = (F).map (K.ιTotal c i q n hi) ≫ g) : f=g := by
  apply IsColimit.hom_ext
    (isColimitOfPreserves F (K.toGradedObject.isColimitCofanMapObj
      (ComplexShape.π c c c) n))
  rintro ⟨⟨⟨i,q⟩,hi⟩⟩
  exact h i q hi
end DerivedBar

end

end OAI
