import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorTwoCone
import OAI.Algebra.AuslanderReiten.Tensor.ExternalEnveloping
import OAI.Algebra.AuslanderReiten.Bar.TBarLift

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) [CharP k 2]
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

def barComparison (n : ℕ) : (AbsoluteBar.complex k R).X (n+3) ⟶
    (AbsoluteBar.complex k R).X n :=
  ModuleCat.ofHom (X := (AbsoluteBar.complex k R).X (n+3))
    (Y := (AbsoluteBar.complex k R).X n) (P q n)

theorem barComparison_chain (n : ℕ) :
    barComparison q (n+1) ≫ (AbsoluteBar.complex k R).d (n+1) n =
      (AbsoluteBar.complex k R).d (n+4) (n+3) ≫ barComparison q n := by
  simp only [AbsoluteBar.complex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact P_differential q (n+1) x

abbrev productTwoConeData : TwoCone.Data (Te ⊗[k] Te) :=
  ExternalTensor.twoConeData k Te Te (AbsoluteBar.complex k R) (AbsoluteBar.complex k R)
    (barComparison q) (barComparison q) (barComparison_chain q) (barComparison_chain q)

abbrev bimoduleTwoConeData : TwoCone.Data (ExternalTensor.EnvelopingProduct k R R) :=
  (productTwoConeData q).restrict (ExternalTensor.envelopingEquiv k R R).symm.toRingHom

abbrev ordinaryK := TwoCone.complex (bimoduleTwoConeData q)

abbrev firstTail := TwoCone.C₁ (bimoduleTwoConeData q)

theorem product_term_finite (n : ℕ) :
    Module.Finite (Te ⊗[k] Te) ((productTwoConeData q).term n) := by
  let (i : ℕ) : Module.Finite Te ((AbsoluteBar.complex k R).X i) := AbsoluteBar.finite k R i
  exact ExternalTensor.term_finite k Te Te (AbsoluteBar.complex k R)
    (AbsoluteBar.complex k R) n

theorem bimodule_term_finite (n : ℕ) :
    Module.Finite (ExternalTensor.EnvelopingProduct k R R) ((bimoduleTwoConeData q).term n) := by
  let := product_term_finite q n
  exact Module.Finite.of_surjective
    (ExternalTensor.envelopingSemilinear k R R ((productTwoConeData q).term n)).toLinearMap
    (ExternalTensor.envelopingSemilinear k R R ((productTwoConeData q).term n)).surjective

theorem firstTail_finite : Module.Finite (ExternalTensor.EnvelopingProduct k R R) (firstTail q) :=
  TwoCone.cokernel_finite _ (bimodule_term_finite q) 1

theorem product_term_projective (n : ℕ) :
    Module.Projective (Te ⊗[k] Te) ((productTwoConeData q).term n) := by
  let (i : ℕ) : Module.Finite Te ((AbsoluteBar.complex k R).X i) := AbsoluteBar.finite k R i
  let (i : ℕ) : Module.Projective Te ((AbsoluteBar.complex k R).X i) :=
    AbsoluteBar.projective k R i
  exact ExternalTensor.term_projective k Te Te (AbsoluteBar.complex k R)
    (AbsoluteBar.complex k R) n

theorem bimodule_term_projective (n : ℕ) :
    Module.Projective (ExternalTensor.EnvelopingProduct k R R) ((bimoduleTwoConeData q).term n) := by
  let := product_term_projective q n
  exact ExternalTensor.enveloping_projective k R R ((productTwoConeData q).term n)

theorem ordinaryK_term_projective (n : ℕ) :
    Module.Projective (ExternalTensor.EnvelopingProduct k R R)
      (TwoCone.term (bimoduleTwoConeData q) n) :=
  TwoCone.term_projective _ (bimodule_term_projective q) n

end ArExplicit.T

end

end OAI
