import OAI.Probability.InvariantIsing.Gaussian.GaussianGramColumns
import OAI.Probability.InvariantIsing.Spectral.PositiveRankOneQuadratic

namespace OAI

/-! Exact leave-one-column identities at the physical Gaussian normalization. -/
noncomputable section
open Matrix
namespace InvariantIsing

def gaussianPatternScaledColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : Fin N → ℝ := (Real.sqrt N)⁻¹ • gaussianGramRawColumn z j

def gaussianGramLeaveResolvent {N m : ℕ} (t : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : Matrix (Fin N) (Fin N) ℝ :=
  (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut z j)⁻¹

lemma gaussianPatternScaledColumn_outer {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) :
    vecMulVec (gaussianPatternScaledColumn z j) (gaussianPatternScaledColumn z j) =
      (1/(N : ℝ)) • vecMulVec (gaussianGramRawColumn z j) (gaussianGramRawColumn z j) := by
  have he : ((Real.sqrt (N : ℝ))⁻¹)^2 = 1/(N : ℝ) := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg N),one_div]
  ext i k
  simp only [gaussianPatternScaledColumn,Matrix.vecMulVec_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((Real.sqrt (N : ℝ))⁻¹)^2*(gaussianGramRawColumn z j i*gaussianGramRawColumn z j k) := by ring
    _ = _ := by rw [he]

lemma gaussianGramLeaveShift_posDef {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    (t • (1 : Matrix (Fin N) (Fin N) ℝ)+gaussianGramLeaveOneOut z j).PosDef :=
  (Matrix.PosDef.one.smul ht).add_posSemidef (gaussianGramLeaveOneOut_posSemidef z j)

lemma gaussianGramLeaveResolvent_quadratic {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    let x := gaussianPatternScaledColumn z j
    x ⬝ᵥ (gaussianGramResolvent t z *ᵥ x) =
      (x ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x))/(1+x ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x)) := by
  have h := positive_rankOne_quadratic _ (gaussianGramLeaveShift_posDef ht z j)
    (gaussianPatternScaledColumn z j)
  rw [gaussianPatternScaledColumn_outer,add_assoc,← gaussianGramLeaveOneOut_decomposition] at h
  exact h

lemma gaussianGramLeaveResolvent_trace {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) :
    let x := gaussianPatternScaledColumn z j
    (gaussianGramLeaveResolvent t z j).trace-(gaussianGramResolvent t z).trace =
      ((gaussianGramLeaveResolvent t z j *ᵥ x) ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x))/
        (1+x ⬝ᵥ (gaussianGramLeaveResolvent t z j *ᵥ x)) := by
  have h := positive_rankOne_trace_difference _ (gaussianGramLeaveShift_posDef ht z j)
    (gaussianPatternScaledColumn z j)
  rw [gaussianPatternScaledColumn_outer,add_assoc,← gaussianGramLeaveOneOut_decomposition] at h
  exact h

end InvariantIsing

end

end OAI
