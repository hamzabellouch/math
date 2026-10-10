import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f : ∀ n : ℕ, P.complex.X (n+3) ⟶ P.complex.X n)

def natCubicCochain : Cochain P.cochainComplex P.cochainComplex 3 :=
  Cochain.mk (fun p q hpq => if hq : q ≤ 0 then
    let m := (-q).toNat
    (P.cochainComplexXIso p (m+3) (by dsimp [m]; omega)).hom ≫ f m ≫
      (P.cochainComplexXIso q m (by dsimp [m]; omega)).inv
    else 0)

theorem natCubicCochain_v (m : ℕ) :
    (natCubicCochain P f).v (-((m+3 : ℕ) : ℤ)) (-(m : ℤ)) (by omega) =
      (P.cochainComplexXIso (-((m+3 : ℕ) : ℤ)) (m+3) rfl).hom ≫ f m ≫
        (P.cochainComplexXIso (-(m : ℤ)) m rfl).inv := by
  cases m <;> rfl

variable [CharP k 2]
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (n+4) (n+3) ≫ f n)

include hf k

theorem natCubicCochain_closed : δ 3 4 (natCubicCochain P f) = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨m,rfl⟩ := Int.exists_eq_neg_ofNat hq
    have hp : p = -((m+4 : ℕ) : ℤ) := by omega
    subst p
    rw [δ_v 3 4 rfl _ _ _ hpq (-((m+1 : ℕ) : ℤ)) (-((m+3 : ℕ) : ℤ)) (by omega) (by omega)]
    rw [natCubicCochain_v P f (m+1), natCubicCochain_v P f m]
    rw [P.cochainComplex_d _ _ (m+1) m rfl rfl,
      P.cochainComplex_d _ _ (m+4) (m+3) rfl rfl]
    have hfour : (4 : ℤ).negOnePow = 1 := by decide
    simp only [hfour, one_smul, Category.assoc, Iso.inv_hom_id_assoc,
      Cochain.zero_v]
    rw [← Category.assoc (f (m+1)), hf m]
    let z := (P.cochainComplexXIso (-((m+4 : ℕ) : ℤ)) (m+4) rfl).hom ≫
      P.complex.d (m+4) (m+3) ≫ f m ≫
        (P.cochainComplexXIso (-(m : ℤ)) m rfl).inv
    change z + z = 0
    rw [← two_smul k z, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]
  · exact (P.cochainComplex.isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _

def natCubicCocycle : Cocycle P.cochainComplex P.cochainComplex 3 :=
  Cocycle.mk (natCubicCochain P f) 4 rfl (natCubicCochain_closed (k := k) P f hf)

end ArExplicit.ResolutionProducts

end

end OAI
