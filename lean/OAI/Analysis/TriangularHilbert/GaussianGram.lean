import OAI.Analysis.TriangularHilbert.CostBlock

namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_pos {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ) (u p : ℝ) :
    0 < weight h u p σ := mul_pos hh (density_pos hσ _)

lemma weightedGram_smul (B : Matrix ι ι ℂ) (c : ℝ) (w : ι → ℝ) :
    weightedGram B (fun i => c * w i) = c • weightedGram B w := by
  have he : Matrix.diagonal (fun i => ((c * w i : ℝ) : ℂ)) =
      c • Matrix.diagonal (fun i => (w i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  unfold weightedGram
  rw [he, Matrix.mul_smul, Matrix.smul_mul]

end
end TriangularHilbert.Heat
end

end OAI
