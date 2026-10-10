import OAI.Analysis.ModularTheory.TracialRightAction
import OAI.Analysis.OperatorAlgebra.AntiunitaryOperatorIdentities

namespace OAI

/-! Strongly exhausting two-sided finite trace corners in the actual
modular Hilbert space. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTracialRightProjection_isStarProjection (S : StandardModularData H) (n : ℕ) :
    IsStarProjection (modularTracialRightAction S (modularFiniteProjection n)) := by
  have hp := modularFiniteProjection_isStarProjection (H := H) n
  change IsStarProjection (antiunitaryConjugate (modularTraceAntiunitary S)
    (star (modularFiniteProjection n)))
  rw [hp.isSelfAdjoint.star_eq]
  exact antiunitaryConjugate_isStarProjection (modularTraceAntiunitary S)
    (modularTraceAntiunitary_involutive S) _ hp

def modularTracialCornerProjection (S : StandardModularData H) (n : ℕ) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  modularFiniteProjection n * modularTracialRightAction S (modularFiniteProjection n)

lemma modularTracialCornerProjection_isStarProjection (S : StandardModularData H) (n : ℕ) :
    IsStarProjection (modularTracialCornerProjection S n) := by
  let p := modularFiniteProjection (H := H) n
  let q := modularTracialRightAction S p
  have hp : IsStarProjection p := modularFiniteProjection_isStarProjection (H := H) n
  have hq : IsStarProjection q := modularTracialRightProjection_isStarProjection S n
  have hc : p * q = q * p := modularTracialRightAction_commutes S p p
    (modularFiniteProjection_mem S n) (modularFiniteProjection_mem S n)
  change IsStarProjection (p * q)
  refine { isSelfAdjoint := ?_, isIdempotentElem := ?_ }
  · change (p * q) * (p * q) = p * q
    calc
      _ = p * (q * p) * q := by noncomm_ring
      _ = p * (p * q) * q := by rw [← hc]
      _ = (p * p) * (q * q) := by noncomm_ring
      _ = p * q := by rw [hp.isIdempotentElem, hq.isIdempotentElem]
  · change star (p * q) = p * q
    rw [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq]
    exact hc.symm

lemma modularTracialCornerProjection_norm_le (S : StandardModularData H) (n : ℕ) :
    ‖modularTracialCornerProjection S n‖ ≤ 1 := by
  have hp := modularFiniteProjection_norm_le (H := H) n
  have hq := (modularTracialRightAction_norm_le S (modularFiniteProjection n)).trans hp
  exact (norm_mul_le _ _).trans ((mul_le_mul hp hq (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1))

lemma modularTracialCornerProjection_strong (S : StandardModularData H)
    (x : Lp H 2 (volume : Measure ℝ)) :
    Tendsto (fun n => modularTracialCornerProjection S n x) atTop (𝓝 x) := by
  have hr : Tendsto (fun n => ‖modularTracialRightAction S (modularFiniteProjection n) x - x‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((modularTracialRightProjection_strong S x).sub (tendsto_const_nhds (x := x))).norm
  have hd : Tendsto (fun n => modularFiniteProjection n
      (modularTracialRightAction S (modularFiniteProjection n) x - x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hr
    exact ((modularFiniteProjection (H := H) n).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (modularFiniteProjection_norm_le n) (norm_nonneg _)).trans_eq
        (one_mul _))
  simpa only [modularTracialCornerProjection, mul_apply_eq_comp, map_sub, sub_add_cancel,
    zero_add] using hd.add (modularFiniteProjection_strong x)

def modularFiniteWeightCorner (S : StandardModularData H) (n : ℕ)
    (T : modularFiniteWeightSpace S) : modularFiniteWeightSpace S :=
  modularFiniteWeightLeft S (modularFiniteProjection n) (modularFiniteProjection_mem S n)
    (modularFiniteWeightRight S T (modularFiniteProjection n) (modularFiniteProjection_mem S n))

lemma modularTracialCornerProjection_vector (S : StandardModularData H) (n : ℕ)
    (T : modularFiniteWeightSpace S) :
    modularTracialCornerProjection S n (modularFiniteWeightMap S T) =
      modularFiniteWeightMap S (modularFiniteWeightCorner S n T) := by
  change modularFiniteProjection n
    (modularTracialRightAction S (modularFiniteProjection n) (modularFiniteWeightMap S T)) = _
  rw [modularTracialRightAction_vector S T _ (modularFiniteProjection_mem S n)]
  exact (modularFiniteWeightMap_left S _ (modularFiniteProjection_mem S n) _).symm

end WeakPureInfiniteness

end

end OAI
