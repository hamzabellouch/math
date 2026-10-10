import OAI.Algebra.AuslanderReiten.Coordinates.TensorTailMap
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorResolution
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionCokernel
import OAI.Algebra.AuslanderReiten.Bar.TwistedBarTensorRegular
import OAI.Algebra.AuslanderReiten.Cones.TwoConeBaseRestriction

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
attribute [local instance 2001] Semiring.toNonAssocSemiring
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "Q₀" => productTwistedTotal q H

def sourceTwist : (R ⊗[k] R) ≃ₐ[k] (R ⊗[k] R) :=
  Algebra.TensorProduct.congr (TrivialExtension.twist H) (TrivialExtension.twist H)

def twistedTensorBarResolution : ProjectiveResolution
    (ExternalTensor.moduleObject k Te Te
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0)
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0)) := by
  letI (n : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).complex.X n) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) n
  exact ExternalTensor.projectiveResolution k Te Te
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))

abbrev productSourceData : TwoCone.Data (Te ⊗[k] Te) where
  term := (Q₀).X
  d n := ((Q₀).d (n+1) n).hom
  first _ := 0
  second _ := 0
  square n := congrArg ModuleCat.Hom.hom ((Q₀).d_comp_d (n+2) (n+1) n)
  first_comm _ := by simp
  second_comm _ := by simp
  comparisons_comm _ := by simp

abbrev sourceData := (productSourceData q H).restrict
  (ExternalTensor.envelopingEquiv k R R).symm.toRingHom

def sourceFourthEquiv : fourthSyzygy q H ≃ₗ[ExternalTensor.EnvelopingProduct k R R]
    TwoCone.BaseCokernel (sourceData q H) 4 := LinearEquiv.refl _ _

theorem source_exact (n : ℕ) :
    Function.Exact ((sourceData q H).d (n+1)) ((sourceData q H).d n) := by
  let (n : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).complex.X n) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) n
  exact ExternalTensor.differential_exact k Te Te
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)) n

private def sourceProductBaseTyped : TwoCone.BaseCokernel (productSourceData q H) 0 ≃ₗ[Te ⊗[k] Te]
    ExternalTensor.moduleObject k Te Te
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0)
      (AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0) :=
  resolutionCokernelEquiv (twistedTensorBarResolution q H)

private def sourceQuotientRestriction : TwoCone.BaseCokernel (sourceData q H) 0 ≃ₗ[
    ExternalTensor.EnvelopingProduct k R R]
    (ExternalTensor.envelopingFunctor k R R).obj
      (ModuleCat.of (ExternalTensor.ProductEnveloping k R R)
        (TwoCone.BaseCokernel (productSourceData q H) 0)) := by
  unfold sourceData
  convert! (TwoCone.baseCokernelRestrictionEquiv (ExternalTensor.envelopingEquiv k R R).symm.toRingHom
    (productSourceData q H) 0).symm using 1

private def sourceProductBaseRestricted := Iso.toLinearEquiv
  ((ExternalTensor.envelopingFunctor k R R).mapIso (sourceProductBaseTyped q H).toModuleIso)

private def sourceToTwistedRegular :=
  (sourceQuotientRestriction q H).trans (sourceProductBaseRestricted q H)

def sourceBaseEquiv : TwoCone.BaseCokernel (sourceData q H) 0 ≃ₗ[
    ExternalTensor.EnvelopingProduct k R R]
    bimoduleEnvelopingObject k (R ⊗[k] R) (TwistedBimodule k (R ⊗[k] R) (sourceTwist q H)) :=
  (sourceToTwistedRegular q H).trans
    (twistedBarTensorBimoduleEquiv k R R (TrivialExtension.twist H) (TrivialExtension.twist H))

theorem source_product_finite (n : ℕ) :
    Module.Finite (Te ⊗[k] Te) ((productSourceData q H).term n) := by
  let (i : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)).X i) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) i
  exact ExternalTensor.term_finite k Te Te
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)) n

theorem source_product_projective (n : ℕ) :
    Module.Projective (Te ⊗[k] Te) ((productSourceData q H).term n) := by
  let (i : ℕ) : Module.Finite Te
      ((AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)).X i) :=
    AbsoluteBar.twistedFinite k R (TrivialExtension.twist H) i
  let (i : ℕ) : Module.Projective Te
      ((AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)).X i) :=
    AbsoluteBar.twistedProjective k R (TrivialExtension.twist H) i
  exact ExternalTensor.term_projective k Te Te
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)) n

theorem source_finite (n : ℕ) :
    Module.Finite (ExternalTensor.EnvelopingProduct k R R) ((sourceData q H).term n) := by
  let := source_product_finite q H n
  exact Module.Finite.of_surjective
    (ExternalTensor.envelopingSemilinear k R R ((productSourceData q H).term n)).toLinearMap
    (ExternalTensor.envelopingSemilinear k R R ((productSourceData q H).term n)).surjective

theorem source_projective (n : ℕ) :
    Module.Projective (ExternalTensor.EnvelopingProduct k R R) ((sourceData q H).term n) := by
  let := source_product_projective q H n
  exact ExternalTensor.enveloping_projective k R R ((productSourceData q H).term n)

end ArExplicit.T

end

end OAI
