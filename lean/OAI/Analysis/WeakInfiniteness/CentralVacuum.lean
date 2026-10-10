import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralState

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace ENNReal

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _

local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _

def fockVacuum : FockSpace := lp.single 2 [] 1

lemma fockVacuum_norm : ‖fockVacuum‖=1 := by
  rw [fockVacuum,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),norm_one]

def oInfinityVacuumState : OInfinity →L[ℂ] ℂ :=
  vectorStateContinuous (oInfinityEvaluation fockRepresentation).toNonUnitalStarAlgHom fockVacuum

lemma oInfinityVacuumState_one : oInfinityVacuumState 1=1 := by
  change inner ℂ fockVacuum ((oInfinityEvaluation fockRepresentation) 1 fockVacuum)=1
  rw [map_one]
  change inner ℂ fockVacuum fockVacuum=1
  simp [fockVacuum]

lemma oInfinityVacuumState_isometry (i : ℕ) : oInfinityVacuumState (oInfinityIsometry i)=0 := by
  change inner ℂ fockVacuum (fockShift i fockVacuum)=0
  simp [fockVacuum,fockShift_single,lp.inner_single_left,lp.single_apply]

def oInfinityCentralStateMap : OInfinity →L[ℂ] OInfinity :=
  (starHomContinuousLinear (StarAlgHom.ofId ℂ OInfinity).toNonUnitalStarAlgHom).comp
    oInfinityVacuumState

lemma oInfinityCentralStateMap_apply (a : OInfinity) :
    oInfinityCentralStateMap a=oInfinityVacuumState a • (1:OInfinity) := by
  change algebraMap ℂ OInfinity (oInfinityVacuumState a)=_
  exact Algebra.algebraMap_eq_smul_one _

lemma oInfinityCentralStateMap_cp : CompletelyPositive oInfinityCentralStateMap := by
  intro n x hx
  have h := vectorStateContinuous_cp (oInfinityEvaluation fockRepresentation).toNonUnitalStarAlgHom
    fockVacuum n x hx
  exact map_nonneg (CStarMatrix.mapₙₐ (StarAlgHom.ofId ℂ OInfinity).toNonUnitalStarAlgHom) h

lemma oInfinityCentralStateMap_norm_le : ‖oInfinityCentralStateMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  rw [oInfinityCentralStateMap_apply,norm_smul,norm_one,mul_one,one_mul]
  have h := vectorStateLinear_bound (oInfinityEvaluation fockRepresentation).toNonUnitalStarAlgHom
    fockVacuum a
  change ‖oInfinityVacuumState a‖≤‖fockVacuum‖^2*‖a‖ at h
  rwa [fockVacuum_norm,one_pow,one_mul] at h

lemma exists_unital_cpc_central_map_killing_generators :
    ∃ Φ : OInfinity →L[ℂ] OInfinity,CompletelyPositive Φ ∧ ‖Φ‖≤1 ∧ Φ 1=1 ∧
      (∀ a z : OInfinity,a*Φ z=Φ z*a) ∧
      (∀ i : ℕ,Φ (oInfinityIsometry i)=0) ∧
      ∀ i : ℕ,‖Φ 1-star (Φ (oInfinityIsometry i))*Φ (oInfinityIsometry i)‖=1 := by
  have hu : oInfinityCentralStateMap 1=1 := by
    change (StarAlgHom.ofId ℂ OInfinity) (oInfinityVacuumState 1)=1
    rw [oInfinityVacuumState_one,map_one]
  have hz (i : ℕ) : oInfinityCentralStateMap (oInfinityIsometry i)=0 := by
    change (StarAlgHom.ofId ℂ OInfinity) (oInfinityVacuumState (oInfinityIsometry i))=0
    rw [oInfinityVacuumState_isometry,map_zero]
  refine ⟨oInfinityCentralStateMap,oInfinityCentralStateMap_cp,oInfinityCentralStateMap_norm_le,
    hu,?_,hz,?_⟩
  · intro a z
    simp only [oInfinityCentralStateMap_apply,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  · intro i
    rw [hu,hz,star_zero,zero_mul,sub_zero,norm_one]

end

end WeakPureInfiniteness
end

end OAI
