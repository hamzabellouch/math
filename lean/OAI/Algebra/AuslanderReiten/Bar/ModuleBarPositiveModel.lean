import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorCentralAction
import OAI.Algebra.AuslanderReiten.Homology.FullPositiveComposite

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
variable (hgen : ∀ n : ℕ, ∀ z : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3),
  ∃ u v : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n),
    z = ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) u +
    ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) v)
include ha hb hgen

def tensorPositiveModel
    (hhom : ∀ g : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        g.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (K : CochainComplex (ModuleCat.{u} (R ⊗[k] S)) ℤ)
    (D : FullPositive.NonnegativeChart (k := k) K (ExternalTensor.moduleObject k R S M N))
    (f : ∀ n, ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n) ≃ₗ[k]
        BinaryKoszul.Piece k n)
    (off : ∀ n, (¬ 3 ∣ n) → ∀ x : ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n, x = 0)
    (lx : ∀ n (x : ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n)),
      f (n+1) (ExternalTensor.coefficientFirst k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) x) =
          BinaryKoszul.mulX k n (f n x))
    (ly : ∀ n (x : ExternalTensor.extCoefficients k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n)),
      f (n+1) (ExternalTensor.coefficientSecond k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) x) =
          BinaryKoszul.mulY k n (f n x)) :
    FullTate.PositiveModel (k := k) K
      ((D.equiv 3).symm (tensorFirst k R S M N p hp))
      ((D.equiv 3).symm (tensorSecond k R S M N r hr)) := by
  apply FullPositive.modelOfComposite K (ExternalTensor.moduleObject k R S M N) D
    (tensorKunneth k R S M N) f (tensorFirst k R S M N p hp) (tensorSecond k R S M N r hr)
  · intro n hn x
    apply (tensorKunneth k R S M N n).injective
    rw [map_zero]
    exact off n hn _
  · intro n x
    rw [tensorFirst_action_of_class k R S M N p hp a ha (3*n) x]
    exact lx n _
  · intro n x
    rw [tensorSecond_action_of_class k R S M N r hr b hb (3*n) x]
    exact ly n _
  · intro n x
    rw [tensorFirst_action_right k R S M N p hp r hr a ha b hb hgen hhom n x]
    exact lx n _
  · intro n x
    rw [tensorSecond_action_right k R S M N p hp r hr a ha b hb hgen hhom n x]
    exact ly n _

end ArExplicit.ModuleBar

end

end OAI
