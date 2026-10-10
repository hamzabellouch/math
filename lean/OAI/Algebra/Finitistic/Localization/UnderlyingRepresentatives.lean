import Mathlib.Algebra.Category.ModuleCat.Algebra
import OAI.Algebra.Finitistic.Localization.ConcreteChainRepresentatives
import OAI.Algebra.Finitistic.Rectification.ColumnComplex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.UnderlyingRepresentatives
open SourceVerdier ConcreteChainRepresentatives
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

abbrev forget : Proj P ⥤ ModuleCat.{u} (QuadraticEncoding.B P)ᵐᵒᵖ :=
  (ProjectiveComplexes.finiteProjective (QuadraticEncoding.B P)).ι

abbrev complex (X : K P) : CochainComplex (ModuleCat.{u} (QuadraticEncoding.B P)ᵐᵒᵖ) ℤ :=
  ((forget P).mapHomologicalComplex (.up ℤ)).obj (representative P X)

theorem projective (X : K P) (n : ℤ) :
    Module.Projective (QuadraticEncoding.B P)ᵐᵒᵖ ((complex P X).X n) :=
  ((representative P X).X n).property.2

theorem finite (X : K P) (n : ℤ) :
    Module.Finite (QuadraticEncoding.B P)ᵐᵒᵖ ((complex P X).X n) :=
  ((representative P X).X n).property.1

attribute [local instance] ExternalTensor.Section4.rightModuleK

theorem finiteDimensional (X : K P) (n : ℤ) :
    FiniteDimensional k ((complex P X).X n) := by
  let := QuadraticEncoding.finiteDimensional P
  let := finite P X n
  exact Module.Finite.trans (QuadraticEncoding.B P)ᵐᵒᵖ ((complex P X).X n)

/-- Genuine boundedness after forgetting the projective subcategory. -/
theorem bounded (X : K P) :
    ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero ((complex P X).X n) := by
  obtain ⟨lo,hi,hlo,hhi⟩ := representative_bounded P X
  let := hlo
  let := hhi
  refine ⟨lo,hi,fun n hn => ?_⟩
  apply (forget P).map_isZero
  rcases hn with hn | hn
  · exact (representative P X).isZero_of_isStrictlyGE lo n hn
  · exact (representative P X).isZero_of_isStrictlyLE hi n hn

/-- The actual chain-representative relation homotopies survive the forgetful functor. -/
def relationHomotopy (na nb nr : ℕ) (X₀ X₁ X₂ : K P)
    (f : Fin na → (representative P X₀ ⟶ representative P X₁))
    (g : Fin nb → (representative P X₁ ⟶ representative P X₂))
    (c : Fin nr → Fin na → Fin nb → k)
    (H : ∀ r, Homotopy (∑ i, ∑ j, c r i j • (f i ≫ g j)) 0) (r : Fin nr) :
    Homotopy
      (∑ i, ∑ j, c r i j •
        (((forget P).mapHomologicalComplex (.up ℤ)).map (f i) ≫
          ((forget P).mapHomologicalComplex (.up ℤ)).map (g j))) 0 := by
  simpa only [Functor.map_sum,Functor.map_smul,Functor.map_comp,Functor.map_zero]
    using (forget P).mapHomotopy (H r)
end LittleFinitistic.UnderlyingRepresentatives

end

end OAI
