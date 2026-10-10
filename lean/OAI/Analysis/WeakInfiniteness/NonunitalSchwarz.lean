import Mathlib
import OAI.Analysis.WeakInfiniteness.CPSchwarz

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

open scoped CStarAlgebra ComplexOrder Topology

open Filter

universe u v

section

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma completelyPositive_schwarz_nonunital_domain {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (hφn : ‖φ‖≤1) (a : A) :
    star (φ a)*φ a≤φ (star a*a) := by
  let l := CStarAlgebra.approximateUnit A
  let hl := CStarAlgebra.increasingApproximateUnit A
  let f : A → B := fun e => φ (star a*a)-φ (star a*e)*φ a-
    star (φ a)*φ (e*a)+star (φ a)*φ a
  have hf : ∀ᶠ e in l,0≤f e := by
    filter_upwards [hl.eventually_nonneg,hl.eventually_norm] with e he hen
    have hestar : star e=e := (IsSelfAdjoint.of_nonneg he).star_eq
    have hφe : φ (star e*e)≤1 := by
      apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
        (completelyPositive_map_nonneg hφ (star_mul_self_nonneg e))).mp
      calc
        _ ≤ ‖φ‖*‖star e*e‖ := φ.le_opNorm _
        _ ≤ ‖star e*e‖ := by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hφn (norm_nonneg (star e*e))
        _ ≤ 1 := by rw [CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg e]
    let R : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![a,e;0,0]
    let M := matrixLinearMap φ (star R*R)
    have hM : 0≤M := matrixLinearMap_nonneg hφ (star_mul_self_nonneg R)
    let V : CStarMatrix (Fin 2) (Fin 2) B := CStarMatrix.ofMatrix !![1,0;-φ a,0]
    have hN := cstarMatrix_diagonal_nonneg (star V*M*V)
      (star_left_conjugate_nonneg hM V) 0
    have heq : (star V*M*V) 0 0=
        φ (star a*a)-φ (star a*e)*φ a-star (φ a)*φ (e*a)+
          star (φ a)*φ (star e*e)*φ a := by
      simp [V,M,R,CStarMatrix.mul_apply,CStarMatrix.star_apply,Fin.sum_univ_two,hestar]
      noncomm_ring
    rw [heq] at hN
    have hP := star_left_conjugate_nonneg (sub_nonneg.mpr hφe) (φ a)
    have h := add_nonneg hN hP
    convert h using 1
    dsimp only [f]
    noncomm_ring
  have hleft : Tendsto (fun e => φ (star a*e)) l (𝓝 (star (φ a))) := by
    rw [← completelyPositive_map_star hφ a]
    exact φ.continuous.tendsto _ |>.comp (hl.tendsto_mul_left (star a))
  have hright : Tendsto (fun e => φ (e*a)) l (𝓝 (φ a)) :=
    φ.continuous.tendsto _ |>.comp (hl.tendsto_mul_right a)
  have ht : Tendsto f l (𝓝 (φ (star a*a)-star (φ a)*φ a)) := by
    have ht' := (((tendsto_const_nhds (x := φ (star a*a))).sub (hleft.mul_const (φ a))).sub
      (hright.const_mul (star (φ a)))).add_const (star (φ a)*φ a)
    convert ht' using 1
    noncomm_ring
  exact sub_nonneg.mp (ge_of_tendsto ht hf)

end

end

end WeakPureInfiniteness
end

end OAI
