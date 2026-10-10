import OAI.Algebra.AuslanderReiten.Homology.FullPositiveModel

namespace OAI

noncomputable section
namespace ArExplicit.FullPositive
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (X : ModuleCat.{u} R)
variable {C : ℕ → Type u} [∀ n, AddCommGroup (C n)] [∀ n, Module k (C n)]

def modelOfComposite (D : NonnegativeChart (k := k) K X)
    (e : ∀ n, Ext X X n ≃ₗ[k] C n)
    (f : ∀ n, C (3*n) ≃ₗ[k] BinaryKoszul.Piece k n)
    (p q : Ext X X 3)
    (off : ∀ n, (¬ 3 ∣ n) → ∀ x : Ext X X n, x=0)
    (lx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (p.comp x (by omega))) = BinaryKoszul.mulX k n (f n (e (3*n) x)))
    (ly : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (q.comp x (by omega))) = BinaryKoszul.mulY k n (f n (e (3*n) x)))
    (rx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (x.comp p (by omega))) = BinaryKoszul.mulX k n (f n (e (3*n) x)))
    (ry : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (x.comp q (by omega))) = BinaryKoszul.mulY k n (f n (e (3*n) x))) :
    FullTate.PositiveModel (k := k) K ((D.equiv 3).symm p) ((D.equiv 3).symm q) :=
  model K X D (fun n => (e (3*n)).trans (f n)) p q off lx ly rx ry

end ArExplicit.FullPositive

end

end OAI
