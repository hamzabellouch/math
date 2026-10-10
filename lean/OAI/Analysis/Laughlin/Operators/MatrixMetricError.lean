import OAI.Analysis.Laughlin.Asymptotics.TruncatedMetricPerturbation

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

noncomputable def entrySum {I : Type*} [Fintype I] (R : I → I → ℝ) : ℝ := ∑ i, ∑ j, |R i j|

theorem entrySum_nonneg {I : Type*} [Fintype I] (R : I → I → ℝ) : 0 ≤ entrySum R := by
  unfold entrySum
  positivity

theorem abs_le_entrySum {I : Type*} [Fintype I] (R : I → I → ℝ) (i j : I) : |R i j| ≤ entrySum R := by
  apply (Finset.single_le_sum (fun k hk => abs_nonneg (R i k)) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum (fun k hk => Finset.sum_nonneg (fun l hl => abs_nonneg (R k l))) (Finset.mem_univ i)

noncomputable def matrixMetricError {I : Type*} [Fintype I] (L Q : ℕ) (R S : I → I → ℝ) : ℝ :=
  entrySum (fun i j => R i j-S i j) + localMetricError L Q * entrySum R

theorem matrixMetricError_nonneg {I : Type*} [Fintype I] (L Q : ℕ) (R S : I → I → ℝ) :
    0 ≤ matrixMetricError L Q R S :=
  add_nonneg (entrySum_nonneg _) (mul_nonneg (localMetricError_nonneg L Q) (entrySum_nonneg R))

theorem matrixMetricError_bound {I : Type*} [Fintype I] (L Q : ℕ) (hL : L ≤ Q)
    (R S : I → I → ℝ) (A : Finset (Fin (Q+1))) (i j : I) :
    |((truncatedDiagonals L Q A)⁻¹)^2*R i j-S i j| ≤ matrixMetricError L Q R S := by
  have he : ((truncatedDiagonals L Q A)⁻¹)^2*R i j-S i j =
      (((truncatedDiagonals L Q A)⁻¹)^2-1)*R i j+(R i j-S i j) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have h₁ := mul_le_mul (truncatedMetricError_bound L Q hL A) (abs_le_entrySum R i j)
    (abs_nonneg _) (localMetricError_nonneg L Q)
  have h₂ := abs_le_entrySum (fun i j => R i j-S i j) i j
  unfold matrixMetricError
  linarith

theorem entrySum_tendsto {I : Type*} [Fintype I] (R : ℕ → I → I → ℝ) (S : I → I → ℝ)
    (hR : ∀ i j, Tendsto (fun Q => R Q i j) atTop (𝓝 (S i j))) :
    Tendsto (fun Q => entrySum (R Q)) atTop (𝓝 (entrySum S)) := by
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact (hR i j).abs

theorem matrixMetricError_tendsto {I : Type*} [Fintype I] (L : ℕ)
    (R : ℕ → I → I → ℝ) (S : I → I → ℝ)
    (hR : ∀ i j, Tendsto (fun Q => R Q i j) atTop (𝓝 (S i j))) :
    Tendsto (fun Q => matrixMetricError L Q (R Q) S) atTop (𝓝 0) := by
  have hd := entrySum_tendsto (fun Q i j => R Q i j-S i j) (fun _ _ => 0)
    (fun i j => by simpa using (hR i j).sub_const (S i j))
  have hr := entrySum_tendsto R S hR
  have h := hd.add ((localMetricError_tendsto L).mul hr)
  simpa [matrixMetricError,entrySum] using h

end Laughlin.Fock

end OAI
