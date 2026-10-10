import OAI.Algebra.Finitistic.Rectification.RectificationTotal
import OAI.Algebra.Finitistic.Rectification.ColumnFinite

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
noncomputable section
namespace ExternalTensor.Section4
universe u
variable {k : Type u} [Field k]
section General
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
variable {L₀ L₁ L₂ : CochainComplex C ℤ} (p : L₁ ⟶ L₀) (q : L₂ ⟶ L₁)
    (h : Homotopy (q ≫ p) 0)

/-- The rectification total has finite-dimensional terms whenever
an additive scalar restriction makes all three columns finite-dimensional. -/
theorem total_finite_after (F : C ⥤ ModuleCat.{u} k) [F.Additive]
    (h₀ : ∀ i, FiniteDimensional k (F.obj (L₀.X i)))
    (h₁ : ∀ i, FiniteDimensional k (F.obj (L₁.X i)))
    (h₂ : ∀ i, FiniteDimensional k (F.obj (L₂.X i))) (i : ℤ) :
    FiniteDimensional k (F.obj ((LittleFinitistic.RectificationTotal.total p q h).X i)) := by
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  apply finite_of_iso k (F.mapIso (LittleFinitistic.RectificationTotal.termIso p q h i) ≪≫
    F.mapBiprod _ _ ≪≫ biprod.mapIso (F.mapBiprod _ _) (Iso.refl _))
  exact biprod_finite k (biprod_finite k (h₂ (i+2)) (h₁ (i+1))) (h₀ i)

end General

variable {B : Type u} [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- The finite-dimensionality conclusion for the manuscript's constructed P,
with no projectivity or finite-dimensionality assumption on P or its columns. -/
theorem induced_total_finite [FiniteDimensional k B]
    (h₀ : ∀ i, Module.Finite Bᵐᵒᵖ (D₀.X i))
    (h₁ : ∀ i, Module.Finite Bᵐᵒᵖ (D₁.X i))
    (h₂ : ∀ i, Module.Finite Bᵐᵒᵖ (D₂.X i)) (i : ℤ) :
    FiniteDimensional k ((forgetK k B).obj
      ((LittleFinitistic.RectificationTotal.total (p s D₀ D₁ D₂ f g)
        (q s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)).X i)) := by
  exact total_finite_after _ _ _ (forgetK k B)
    (fun n => (columns_finite s D₀ D₁ D₂ f g h₀ h₁ h₂ n).1)
    (fun n => (columns_finite s D₀ D₁ D₂ f g h₀ h₁ h₂ n).2.1)
    (fun n => (columns_finite s D₀ D₁ D₂ f g h₀ h₁ h₂ n).2.2) i
end ExternalTensor.Section4

end

end OAI
