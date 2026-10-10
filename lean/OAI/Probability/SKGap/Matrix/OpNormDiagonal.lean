import Mathlib
import OAI.Probability.SKGap.Matrix.OpNorm

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_diagonal_eq (d : ι → ℝ) : opNorm (diagonal d) = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

lemma opNorm_diagonal_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) :
    opNorm (diagonal d) ≤ C := by
  rw [opNorm_diagonal_eq]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun i => by simpa only [Real.norm_eq_abs] using hd i)

lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℝ) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 : Matrix ι ι ℝ)‖ ≤ _
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

lemma opNorm_sub (M N : Matrix ι ι ℝ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (M-N)‖ ≤ _
  rw [map_sub]
  exact norm_sub_le _ _

lemma real_sandwich_opNorm (D V : Matrix ι ι ℝ) :
    opNorm (D*V*D) ≤ opNorm D^2*opNorm V := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (D*V*D)‖ ≤
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D‖^2*‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V‖
  simp only [map_mul]
  have h := (norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D*Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V)
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) D) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) V))
      (norm_nonneg _))
  exact h.trans_eq (by ring)

lemma real_sandwich_stability_norm (D C M : Matrix ι ι ℝ) :
    opNorm (1-D*(M-C)*D) ≤ 1+opNorm D^2*(opNorm M+opNorm C) := by
  calc
    _ ≤ opNorm (1 : Matrix ι ι ℝ)+opNorm (D*(M-C)*D) := opNorm_sub _ _
    _ ≤ 1+opNorm D^2*(opNorm M+opNorm C) :=
      add_le_add opNorm_one_le ((real_sandwich_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (opNorm_sub _ _) (sq_nonneg _)))

end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
