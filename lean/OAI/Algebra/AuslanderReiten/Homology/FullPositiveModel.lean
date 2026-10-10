import OAI.Algebra.AuslanderReiten.Complete.FullTateModel
import OAI.Algebra.AuslanderReiten.Ext.ExtIsoCongr

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FullPositive
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (X : ModuleCat.{u} R)
open CompleteComparison TateKoszul
local notation "H" => CohomologyClass K K

structure NonnegativeChart where
  equiv : ∀ n : ℕ, H (n:ℤ) ≃ₗ[k] Ext X X n
  product : ∀ (n m : ℕ) (x : H (n:ℤ)) (y : H (m:ℤ)),
    equiv (n+m) (degreeEquiv (k := k) H (show (n:ℤ)+(m:ℤ)=((n+m:ℕ):ℤ) by omega)
      (fullHomProduct x y)) = (equiv n x).comp (equiv m y) rfl

def atDegree (D : NonnegativeChart (k := k) K X) (a : ℤ) (n : ℕ) (ha : a=(n:ℤ)) : H a ≃ₗ[k] Ext X X n :=
  (degreeEquiv (k := k) H ha).trans (D.equiv n)

theorem atDegree_product (D : NonnegativeChart (k := k) K X) (a b : ℤ) (n m r : ℕ)
    (ha : a=(n:ℤ)) (hb : b=(m:ℤ)) (hr : n+m=r)
    (x : H a) (y : H b) :
    atDegree K X D (a+b) r (by omega) (fullHomProduct x y) =
      (atDegree K X D a n ha x).comp (atDegree K X D b m hb y) hr := by
  subst r
  subst a
  subst b
  exact D.product n m x y

def positive (D : NonnegativeChart (k := k) K X)
    (f : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n) (n : ℕ) : H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n :=
  (atDegree K X D (3*(n:ℤ)) (3*n) (by omega)).trans (f n)

theorem positive_transport (D : NonnegativeChart (k := k) K X)
    (f : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n) (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a) :
    positive K X D f n (degreeEquiv (k := k) H ha v) =
      f n (atDegree K X D a (3*n) (by omega) v) := by
  subst a
  rfl

def model (D : NonnegativeChart (k := k) K X)
    (f : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n)
    (p q : Ext X X 3)
    (off : ∀ (n : ℕ), (¬ 3 ∣ n) → ∀ x : Ext X X n, x=0)
    (lx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (p.comp x (by omega : 3+3*n=3*(n+1))) = BinaryKoszul.mulX k n (f n x))
    (ly : ∀ n (x : Ext X X (3*n)),
      f (n+1) (q.comp x (by omega : 3+3*n=3*(n+1))) = BinaryKoszul.mulY k n (f n x))
    (rx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (x.comp p (by omega : 3*n+3=3*(n+1))) = BinaryKoszul.mulX k n (f n x))
    (ry : ∀ n (x : Ext X X (3*n)),
      f (n+1) (x.comp q (by omega : 3*n+3=3*(n+1))) = BinaryKoszul.mulY k n (f n x)) :
    FullTate.PositiveModel (k := k) K ((D.equiv 3).symm p) ((D.equiv 3).symm q) where
  positive := positive K X D f
  outside a ha hn := by
    obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le ha
    have hd : ¬ 3 ∣ n := by
      rintro ⟨m,hm⟩
      exact hn m (by omega)
    exact ⟨fun x y => (D.equiv n).injective ((off n hd _).trans (off n hd _).symm)⟩
  right_x a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct v ((D.equiv 3).symm p))) = _
    erw [positive_transport, atDegree_product K X D a 3 (3*n) 3 (3*(n+1)) (by omega) rfl (by omega)]
    change f (n+1) ((atDegree K X D a (3*n) (by omega) v).comp (D.equiv 3 ((D.equiv 3).symm p)) _) = _
    rw [LinearEquiv.apply_symm_apply, rx, positive_transport]
  right_y a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct v ((D.equiv 3).symm q))) = _
    erw [positive_transport, atDegree_product K X D a 3 (3*n) 3 (3*(n+1)) (by omega) rfl (by omega)]
    change f (n+1) ((atDegree K X D a (3*n) (by omega) v).comp (D.equiv 3 ((D.equiv 3).symm q)) _) = _
    rw [LinearEquiv.apply_symm_apply, ry, positive_transport]
  left_x a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct ((D.equiv 3).symm p) v)) = _
    erw [positive_transport, atDegree_product K X D 3 a 3 (3*n) (3*(n+1)) rfl (by omega) (by omega)]
    change f (n+1) ((D.equiv 3 ((D.equiv 3).symm p)).comp (atDegree K X D a (3*n) (by omega) v) _) = _
    rw [LinearEquiv.apply_symm_apply, lx, positive_transport]
  left_y a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct ((D.equiv 3).symm q) v)) = _
    erw [positive_transport, atDegree_product K X D 3 a 3 (3*n) (3*(n+1)) rfl (by omega) (by omega)]
    change f (n+1) ((D.equiv 3 ((D.equiv 3).symm q)).comp (atDegree K X D a (3*n) (by omega) v) _) = _
    rw [LinearEquiv.apply_symm_apply, ly, positive_transport]

end ArExplicit.FullPositive

end

end OAI
