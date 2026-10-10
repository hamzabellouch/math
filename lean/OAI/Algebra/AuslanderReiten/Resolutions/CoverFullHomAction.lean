import OAI.Algebra.AuslanderReiten.Coordinates.CubicShiftNaturality
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedProducts
import OAI.Algebra.AuslanderReiten.Complete.TateKoszul

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]

private theorem fullHom_composition_degree {K L M : CochainComplex C ℤ}
    {a b d : ℤ} (h : a+b=d) (x : CohomologyClass K L a) (y : CohomologyClass L M b) :
    (fullHomShiftedHomotopyEquiv k K M d).symm
      (ShiftedHom.comp (fullHomShiftedHomotopyEquiv k K L a x)
        (fullHomShiftedHomotopyEquiv k L M b y) (by omega : b+a=d)) =
      TateKoszul.degreeEquiv (k := k) (fun n => CohomologyClass K M n) h (fullHomProduct x y) := by
  subst d
  apply (fullHomShiftedHomotopyEquiv k K M (a+b)).injective
  simp only [LinearEquiv.apply_symm_apply]
  exact (fullHomShiftedHomotopyEquiv_product k x y).symm

variable (K : CochainComplex C ℤ)
variable (Y : ℕ → HomotopyCategory C (ComplexShape.up ℤ)) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)
variable (u : ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≅ Y 0) (c : ∀ n, Y (n+3) ⟶ Y n)

def coverFullHomEquiv (n : ℕ) (a : ℤ) :
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶ (Y n)⟦a⟧) ≃ₗ[k] CohomologyClass K K (a-(n : ℤ)) :=
  (shiftedNegativeHomEquiv (n : ℤ) (basedIteration Y s u n) k ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) a).trans
    (fullHomShiftedHomotopyEquiv k K K (a-(n : ℤ))).symm

theorem coverFullHom_action
    (hs : ∀ n, c n ≫ (s n).hom = (s (n+3)).hom ≫ (c (n+1))⟦(1 : ℤ)⟧')
    (p : CohomologyClass K K 3)
    (hp : fullHomShiftedHomotopyEquiv k K K 3 p = coverCubic Y s u c)
    (n : ℕ) (a : ℤ) (v : ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶ (Y (n+3))⟦a⟧) :
    coverFullHomEquiv k K Y s u n a (v ≫ (c n)⟦a⟧') =
      TateKoszul.degreeEquiv (k := k) (fun i => CohomologyClass K K i)
        (by omega : (a-((n+3 : ℕ) : ℤ))+3=a-(n : ℤ))
        (fullHomProduct (coverFullHomEquiv k K Y s u (n+3) a v) p) := by
  unfold coverFullHomEquiv
  simp only [LinearEquiv.trans_apply, shiftedNegativeHomEquiv_comp]
  rw [coverCubic_action Y s u c hs n a v, ← hp]
  simpa only [LinearEquiv.apply_symm_apply] using
    (fullHom_composition_degree k (K := K) (L := K) (M := K)
      (a := a-((n+3 : ℕ) : ℤ)) (b := 3) (d := a-(n : ℤ)) (by omega)
      ((fullHomShiftedHomotopyEquiv k K K (a-((n+3 : ℕ) : ℤ))).symm
        (ShiftedHom.comp v
          (negativeShiftIso ((n+3 : ℕ) : ℤ) (basedIteration Y s u (n+3))).hom (by omega))) p)

end ArExplicit

end

end OAI
