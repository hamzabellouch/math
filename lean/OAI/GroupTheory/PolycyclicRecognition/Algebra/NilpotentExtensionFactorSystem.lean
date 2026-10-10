import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupExtensionFactorSystem
import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeInnerLogarithm

namespace OAI

/-! # The actual real factor system of a nilpotent-kernel extension

Its failure to be an action is exactly the exponential of the inner Lie
derivation obtained from the section defect.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)
open GroupExtensionSection
open scoped Manifold ContDiff

def extensionFactorSystem : NonabelianFactorSystem C.carrier Q where
  action q := C.automorphism (S.conjAct (σ q))
  factor q r := C.equiv (factor S σ q r)
  action_one := by rw [hσ, map_one, C.automorphism_one]
  factor_one_left q := by rw [factor_one_left S σ hσ, map_one, Subgroup.coe_one]
  factor_one_right q := by rw [factor_one_right S σ hσ, map_one, Subgroup.coe_one]
  action_mul q r := by
    rw [← C.automorphism_mul, section_action_mul, C.automorphism_mul]
    congr 1
    apply DFunLike.ext
    intro v
    exact C.automorphism_inner_apply _ v
  cocycle q r s := by
    have h := congrArg (fun n : N => (C.equiv n : C.carrier)) (factor_cocycle S σ q r s)
    simpa only [map_mul, Subgroup.coe_mul, C.automorphism_on_lattice] using h

/-- Smoothness is proved from the lattice polynomial extension. -/
theorem extensionFactorSystem_smooth (q : Q) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞
      ((C.extensionFactorSystem S σ hσ).action q) :=
  C.automorphism_smooth _

/-- The exact defect formula on continuous linear operators. -/
theorem extension_linear_defect (q r : Q) :
    LinearMap.toContinuousLinearMap (C.automorphismLinear (S.conjAct (σ q))) *
        LinearMap.toContinuousLinearMap (C.automorphismLinear (S.conjAct (σ r))) =
      NormedSpace.exp (LinearMap.toContinuousLinearMap
          (LieAlgebra.ad ℝ C.carrier (C.equiv (factor S σ q r)))) *
        LinearMap.toContinuousLinearMap (C.automorphismLinear (S.conjAct (σ (q * r)))) := by
  have h : C.automorphismLinear (S.conjAct (σ q)) *
      C.automorphismLinear (S.conjAct (σ r)) =
      C.automorphismLinear (MulAut.conj (factor S σ q r)) *
        C.automorphismLinear (S.conjAct (σ (q * r))) := by
    rw [← map_mul, section_action_mul, map_mul]
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) C.carrier
  have he := congrArg E h
  simp only [map_mul] at he
  change LinearMap.toContinuousLinearMap (C.automorphismLinear (S.conjAct (σ q))) *
      LinearMap.toContinuousLinearMap (C.automorphismLinear (S.conjAct (σ r))) =
      LinearMap.toContinuousLinearMap (C.automorphismLinear (MulAut.conj (factor S σ q r))) *
        LinearMap.toContinuousLinearMap (C.automorphismLinear (S.conjAct (σ (q * r)))) at he
  rw [C.automorphismLinear_inner_exp] at he
  exact he

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
