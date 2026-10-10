import OAI.Algebra.AuslanderReiten.Resolutions.CoverStepCoordinates

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K : CochainComplex C ℤ}
local notation "HC" => HomotopyCategory C (ComplexShape.up ℤ)
private abbrev sourceObject (K : CochainComplex C ℤ) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K
local notation "X₀" => sourceObject K

private theorem fullHom_coordinates_degree {a b i j : ℤ} (h : a=b)
    {Y : HC} (x : X₀ ⟶ Y⟦i⟧) (y : Y ⟶ X₀⟦j⟧)
    (ha : j+i=a) (hb : j+i=b) :
    (fullHomShiftedHomotopyEquiv k K K b).symm (ShiftedHom.comp x y hb) =
      TateKoszul.degreeEquiv (k := k) (fun d => CohomologyClass K K d) h
        ((fullHomShiftedHomotopyEquiv k K K a).symm (ShiftedHom.comp x y ha)) := by
  subst b
  rfl

private theorem shiftedNegative_step_at (Y Z : HC) (n : ℤ)
    (e : X₀ ≅ Y⟦n⟧) (s : Y ≅ Z⟦(1 : ℤ)⟧) (t : X₀ ≅ Z⟦n+1⟧)
    (ht : t.hom = ShiftedHom.comp e.hom s.hom (add_comm 1 n))
    (a d : ℤ) (hd : d=a-n) (v : X₀ ⟶ Y⟦a⟧) :
    ShiftedHom.comp (ShiftedHom.comp v s.hom (add_comm 1 a))
      (negativeShiftIso (n+1) t).hom (by omega : -(n+1)+(a+1)=d) =
      ShiftedHom.comp v (negativeShiftIso n e).hom (by omega : -n+a=d) := by
  subst d
  exact shiftedNegative_step n e s t ht a v

theorem coverStepFullHom (Y Z : HC) (n m : ℤ) (hm : m=n+1)
    (e : X₀ ≅ Y⟦n⟧) (s : Y ≅ Z⟦(1 : ℤ)⟧) (t : X₀ ≅ Z⟦m⟧)
    (ht : t.hom = ShiftedHom.comp e.hom s.hom (by omega : 1+n=m))
    (a : ℤ) (v : X₀ ⟶ Y⟦a⟧) :
    (fullHomShiftedHomotopyEquiv k K K (a+1-m)).symm
      (shiftedNegativeHomEquiv m t k X₀ (a+1)
        (ShiftedHom.comp v s.hom (add_comm 1 a))) =
    TateKoszul.degreeEquiv (k := k) (fun d => CohomologyClass K K d)
      (by omega : a-n=a+1-m)
      ((fullHomShiftedHomotopyEquiv k K K (a-n)).symm
        (shiftedNegativeHomEquiv n e k X₀ a v)) := by
  subst m
  simp only [shiftedNegativeHomEquiv_comp]
  have hh := shiftedNegative_step_at Y Z n e s t ht a (a+1-(n+1)) (by omega) v
  rw [hh]
  exact fullHom_coordinates_degree k (by omega) v (negativeShiftIso n e).hom _ _

end ArExplicit

end

end OAI
