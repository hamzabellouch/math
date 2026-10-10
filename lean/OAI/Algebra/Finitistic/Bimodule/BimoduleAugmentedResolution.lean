import OAI.Algebra.Finitistic.Bimodule.BimoduleBarResolution
import OAI.Algebra.Finitistic.Tensor.BalancedProjectiveLeft

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev bimoduleStalk (X : ModuleCat.{u} (Enveloping k B)) : BiComplex k B :=
  (HomologicalComplex.single (ModuleCat (Enveloping k B)) (.up ℤ) 0).obj X

/-- Actual bounded right-projective resolution data, including the bimodule
augmentation and its quasi-isomorphism; no tensor comparison is assumed. -/
structure AugmentedProjective (P : BiComplex k B) (X : ModuleCat.{u} (Enveloping k B)) where
  data : BoundedProjective k B P
  augmentation : P ⟶ bimoduleStalk k B X
  quasiIso : QuasiIso augmentation

namespace AugmentedProjective
variable {k B} {P : BiComplex k B} {X : ModuleCat.{u} (Enveloping k B)}
variable (res : AugmentedProjective k B P X)

/-- The augmentation induces the concrete finite-total transformation. -/
def tensorAugmentation : functor k B P res.data.degrees
    (intervalDegrees_strictMono res.data.lower res.data.upper) ⟶
    functor k B (bimoduleStalk k B X) res.data.degrees
      (intervalDegrees_strictMono res.data.lower res.data.upper) :=
  leftTensorNat res.data.degrees (intervalDegrees_strictMono res.data.lower res.data.upper)
    res.augmentation

/-- Each horizontal augmentation row is a B-linear quasi-isomorphism on a
projective left-module input, including every term of the total bar. -/
theorem projectiveRow_quasiIso (N : ModuleCat.{u} B) [Projective N] :
    QuasiIso (((BimoduleBalancedTensor.functor k B
      (BalancedTensor.ScalarLeftModule k B N)).mapHomologicalComplex (.up ℤ)).map
        res.augmentation) := by
  let : Module.Projective B (BalancedTensor.ScalarLeftModule k B N) :=
    inferInstanceAs (Module.Projective B N)
  let := res.quasiIso
  exact BimoduleBalancedTensor.projectiveInput_quasiIso k B _ res.augmentation

/-- In particular the actual resolution supplied by DerivedBar has all the
projective rows needed for the remaining finite-total quasi-isomorphism proof. -/
theorem barRow_quasiIso (Z : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    QuasiIso (((BimoduleBalancedTensor.functor k B
      (BalancedTensor.ScalarLeftModule k B ((DerivedBar.barTotal k B Z).X n))).mapHomologicalComplex
        (.up ℤ)).map res.augmentation) := by
  let : Projective ((DerivedBar.barTotal k B Z).X n) := DerivedBar.barTotal_projective k B Z n
  exact projectiveRow_quasiIso res _
end AugmentedProjective
end LittleFinitistic.BimoduleTotal

end

end OAI
