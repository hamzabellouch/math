import OAI.Algebra.AuslanderReiten.Cones.BimoduleTwoCone
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorResolution
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionCokernel

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

def tensorBarResolution : ProjectiveResolution
    (ExternalTensor.moduleObject k Te Te (AbsoluteBar.moduleObject k R 0)
      (AbsoluteBar.moduleObject k R 0)) := by
  letI (n : ℕ) : Module.Finite Te ((AbsoluteBar.resolution k R).complex.X n) :=
    AbsoluteBar.finite k R n
  exact ExternalTensor.projectiveResolution k Te Te (AbsoluteBar.resolution k R)
    (AbsoluteBar.resolution k R)

theorem product_exact (n : ℕ) :
    Function.Exact ((productTwoConeData q).d (n+1)) ((productTwoConeData q).d n) := by
  let (degree : ℕ) : Module.Finite Te ((AbsoluteBar.resolution k R).complex.X degree) :=
    AbsoluteBar.finite k R degree
  exact ExternalTensor.differential_exact k Te Te (AbsoluteBar.resolution k R)
    (AbsoluteBar.resolution k R) n

theorem bimodule_exact (n : ℕ) :
    Function.Exact ((bimoduleTwoConeData q).d (n+1)) ((bimoduleTwoConeData q).d n) :=
  product_exact q n

def productBaseCokernelEquiv :=
  resolutionCokernelEquiv (tensorBarResolution q)

end ArExplicit.T

end

end OAI
