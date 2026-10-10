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

include k in
theorem intUnit_smul_charTwo [CharP k 2] {M : Type u} [AddCommGroup M] [Module k M]
    (a : ℤˣ) (x : M) : a • x = x := by
  rcases Int.units_eq_one_or a with rfl | rfl
  · exact one_smul _ x
  · change (-1 : ℤ) • x = x
    rw [neg_one_zsmul]
    have hx : x+x=0 := by
      rw [← two_smul k x, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
    exact (eq_neg_iff_add_eq_zero.mpr hx).symm

variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable (r : ℕ) (f : ∀ n : ℕ, P.complex.X (r+n) ⟶ Q.complex.X n)

def natComparisonCochain : Cochain P.cochainComplex Q.cochainComplex (r : ℤ) :=
  Cochain.mk (fun p q hpq => if hq : q ≤ 0 then
    let m := (-q).toNat
    (P.cochainComplexXIso p (r+m) (by dsimp [m]; omega)).hom ≫ f m ≫
      (Q.cochainComplexXIso q m (by dsimp [m]; omega)).inv
    else 0)

theorem natComparisonCochain_v (m : ℕ) :
    (natComparisonCochain P Q r f).v (-((r+m : ℕ) : ℤ)) (-(m : ℤ)) (by omega) =
      (P.cochainComplexXIso (-((r+m : ℕ) : ℤ)) (r+m) rfl).hom ≫ f m ≫
        (Q.cochainComplexXIso (-(m : ℤ)) m rfl).inv := by
  cases m <;> rfl

theorem natComparisonCochain_v_of_eq (p : ℤ) (m : ℕ) (hp : p+(r : ℤ)=-(m : ℤ)) :
    (natComparisonCochain P Q r f).v p (-(m : ℤ)) hp =
      (P.cochainComplexXIso p (r+m) (by omega)).hom ≫ f m ≫
        (Q.cochainComplexXIso (-(m : ℤ)) m rfl).inv := by
  cases m <;> rfl

variable [CharP k 2]
variable (hf : ∀ n, f (n+1) ≫ Q.complex.d (n+1) n =
  P.complex.d (r+(n+1)) (r+n) ≫ f n)
include hf k

theorem natComparisonCochain_closed :
    δ (r : ℤ) ((r : ℤ)+1) (natComparisonCochain P Q r f) = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨m,rfl⟩ := Int.exists_eq_neg_ofNat hq
    have hp : p = -((r+(m+1) : ℕ) : ℤ) := by omega
    subst p
    rw [δ_v _ _ rfl _ _ _ hpq (-((m+1 : ℕ) : ℤ)) (-((r+m : ℕ) : ℤ))
      (by omega) (by omega)]
    rw [natComparisonCochain_v P Q r f (m+1), natComparisonCochain_v P Q r f m]
    rw [Q.cochainComplex_d _ _ (m+1) m rfl rfl,
      P.cochainComplex_d _ _ (r+(m+1)) (r+m) rfl rfl]
    rw [intUnit_smul_charTwo (k := k)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Cochain.zero_v]
    rw [← Category.assoc (f (m+1)), hf m]
    let z := (P.cochainComplexXIso (-((r+(m+1) : ℕ) : ℤ)) (r+(m+1)) rfl).hom ≫
      P.complex.d (r+(m+1)) (r+m) ≫ f m ≫
        (Q.cochainComplexXIso (-(m : ℤ)) m rfl).inv
    change z+z=0
    rw [← two_smul k z, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
  · exact (Q.cochainComplex.isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _

def natComparisonCocycle : Cocycle P.cochainComplex Q.cochainComplex (r : ℤ) :=
  Cocycle.mk (natComparisonCochain P Q r f) _ rfl
    (natComparisonCochain_closed (k := k) P Q r f hf)

end ArExplicit.ResolutionProducts

end

end OAI
