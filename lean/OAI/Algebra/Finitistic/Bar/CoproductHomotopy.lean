import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar

section
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasColimitsOfShape (Discrete ℕ) C] {ι : Type w} {c : ComplexShape ι}
  (F : Discrete ℕ ⥤ HomologicalComplex C c) (s : Cocone F) (hs : IsColimit s)
  {Y : HomologicalComplex C c} (f g : s.pt ⟶ Y)
  (h : ∀ r, Homotopy (s.ι.app r ≫ f) (s.ι.app r ≫ g))

def coproductHomotopyHom (i j : ι) : s.pt.X i ⟶ Y.X j :=
  (isColimitOfPreserves (HomologicalComplex.eval C c i) hs).desc
    { pt := Y.X j, ι := Discrete.natTrans (fun r => (h r).hom i j) }

@[reassoc] theorem ι_coproductHomotopyHom (i j : ι) (r : Discrete ℕ) :
    (s.ι.app r).f i ≫ coproductHomotopyHom F s hs f g h i j = (h r).hom i j :=
  (isColimitOfPreserves (HomologicalComplex.eval C c i) hs).fac _ r

/-- Homotopies out of the summands assemble through the actual degreewise
coproduct, so equality after the homotopy quotient is still detected summandwise. -/
def coproductHomotopy : Homotopy f g where
  hom := coproductHomotopyHom F s hs f g h
  zero i j hij := by
    apply (isColimitOfPreserves (HomologicalComplex.eval C c i) hs).hom_ext
    intro r
    change (s.ι.app r).f i ≫ coproductHomotopyHom F s hs f g h i j = _
    rw [ι_coproductHomotopyHom, CategoryTheory.Limits.comp_zero]
    exact (h r).zero i j hij
  comm i := by
    apply (isColimitOfPreserves (HomologicalComplex.eval C c i) hs).hom_ext
    intro r
    change (s.ι.app r).f i ≫ f.f i = (s.ι.app r).f i ≫
      (s.pt.d i (c.next i) ≫ coproductHomotopyHom F s hs f g h (c.next i) i +
       coproductHomotopyHom F s hs f g h i (c.prev i) ≫ Y.d (c.prev i) i + g.f i)
    simp only [Preadditive.comp_add]
    erw [(s.ι.app r).comm_assoc i (c.next i)]
    rw [ι_coproductHomotopyHom, ι_coproductHomotopyHom_assoc]
    exact (h r).comm i

end
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasColimitsOfShape (Discrete ℕ) C] {ι : Type w} {c : ComplexShape ι}
  (F : Discrete ℕ ⥤ HomologicalComplex C c) (s : Cocone F) (hs : IsColimit s)
local notation "Q" => HomotopyCategory.quotient C c

def homotopyCoconeLift (t : Cocone (F ⋙ Q)) : Cocone F where
  pt := t.pt.as
  ι := Discrete.natTrans (fun r => (t.ι.app r).out)

/-- The actual coproduct survives the homotopy quotient. Both existence and
uniqueness are proved; the latter assembles the component homotopies. -/
def homotopyCoproductIsColimit : IsColimit ((Q).mapCocone s) where
  desc t := (Q).map (hs.desc (homotopyCoconeLift F t))
  fac t r := by
    change (Q).map (s.ι.app r) ≫ (Q).map (hs.desc (homotopyCoconeLift F t)) = _
    rw [← Functor.map_comp, hs.fac]
    exact HomotopyCategory.quotient_map_out _
  uniq t m hm := by
    have h : Homotopy m.out (hs.desc (homotopyCoconeLift F t)) :=
      coproductHomotopy F s hs m.out (hs.desc (homotopyCoconeLift F t)) (fun r =>
        HomotopyCategory.homotopyOfEq _ _ (by
          erw [hs.fac]
          have hmr := hm r
          change (Q).map (s.ι.app r) ≫ m = t.ι.app r at hmr
          simp only [Functor.map_comp, homotopyCoconeLift, Discrete.natTrans_app,
            HomotopyCategory.quotient_map_out]
          exact hmr))
    exact (HomotopyCategory.quotient_map_out m).symm.trans
      (HomotopyCategory.eq_of_homotopy _ _ h)
end DerivedBar

end

end OAI
