import OAI.Analysis.KadisonSimilarity.Hyperreflexivity
import OAI.Analysis.KadisonSimilarity.Representation.FiniteAmplificationReduction

namespace OAI

/-! The elementary direction of the Arveson distance identity: subtracting
an element of the commutant bounds every matrix commutator by twice the
distance. The converse distance estimate remains a separate input. -/

noncomputable section
namespace KadisonSimilarity
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem amplified_commutator_eq_zero_of_mem
    (M : VonNeumannAlgebra H) (S : H →L[ℂ] H) (hS : S ∈ M)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M.commutant) :
    commutator (amplify S n) (matrixOperator X) = 0 := by
  rw [commutator_amplify_matrixOperator]
  have he (i j : Fin n) : commutator S (X i j) = 0 := by
    have h := VonNeumannAlgebra.mem_commutant_iff.mp (hX i j) S hS
    exact sub_eq_zero.mpr h
  have hfun : (fun i j => commutator S (X i j)) =
      (0 : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) := by
    funext i j
    exact he i j
  rw [hfun]
  apply ContinuousLinearMap.ext
  intro ξ
  apply PiLp.ext
  intro i
  simp [matrixOperator]

theorem matrix_commutator_le_twice_distance
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {n : ℕ} (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M.commutant) (hXn : ‖matrixOperator X‖ ≤ 1) :
    ‖commutator (amplify T n) (matrixOperator X)‖ ≤
      2 * Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  have hdist : ‖commutator (amplify T n) (matrixOperator X)‖ / 2 ≤
      Metric.infDist T (M : Set (H →L[ℂ] H)) := by
    apply (Metric.le_infDist ⟨0, M.zero_mem⟩).mpr
    intro S hS
    have hzero := amplified_commutator_eq_zero_of_mem M S hS X hX
    have hb := norm_commutator_le_of_approx (amplify T n) (amplify S n)
      (matrixOperator X) (a := 0) (d := ‖T - S‖)
      (by rw [hzero, norm_zero]) (norm_amplify_sub_le T S n)
    have hc : 2 * ‖T - S‖ * ‖matrixOperator X‖ ≤ 2 * ‖T - S‖ :=
      mul_le_of_le_one_right (by positivity) hXn
    rw [dist_eq_norm]
    linarith
  linarith

/-- The completely bounded commutator norm never exceeds twice the distance. -/
theorem completeCommutatorNorm_le_twice_distance
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    completeCommutatorNorm M.commutant T ≤
      ENNReal.ofReal (2 * Metric.infDist T (M : Set (H →L[ℂ] H))) := by
  refine iSup_le fun n => iSup_le fun X => iSup_le fun hX => iSup_le fun hXn => ?_
  exact ENNReal.ofReal_le_ofReal (matrix_commutator_le_twice_distance M T X hX hXn)

/-- Thus only the reverse distance bound is needed for the exact identity. -/
theorem arvesonDistanceFormula_iff_reverse_bound
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    ArvesonDistanceFormula M T ↔
      ENNReal.ofReal (2 * Metric.infDist T (M : Set (H →L[ℂ] H))) ≤
        completeCommutatorNorm M.commutant T := by
  constructor
  · intro h
    exact h.ge
  · intro h
    exact le_antisymm (completeCommutatorNorm_le_twice_distance M T) h

end KadisonSimilarity

end

end OAI
