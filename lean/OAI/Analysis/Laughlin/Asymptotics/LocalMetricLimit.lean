import OAI.Analysis.Laughlin.Exterior.OccupationMetric

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Topology
open Filter

noncomputable def localMetricError (L Q : ℕ) : ℝ :=
  ‖fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2 - 1‖

theorem localMetricError_nonneg (L Q : ℕ) : 0 ≤ localMetricError L Q := norm_nonneg _

theorem localMetricError_tendsto (L : ℕ) :
    Tendsto (localMetricError L) atTop (𝓝 0) := by
  have h := ((localMetricDiagonals_tendsto L).sub
    (tendsto_const_nhds (x := fun _ : Finset (Fin (L+1)) => (1 : ℝ)))).norm
  change Tendsto (fun Q : ℕ => ‖(fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2) -
    (fun _ : Finset (Fin (L+1)) => (1 : ℝ))‖) atTop (𝓝 0)
  simpa only [sub_self,norm_zero] using h

theorem localMetricError_bound (L Q : ℕ) (A : Finset (Fin (L+1))) :
    |((localDiagonals L Q A)⁻¹)^2-1| ≤ localMetricError L Q := by
  have h := norm_le_pi_norm (fun A : Finset (Fin (L+1)) => ((localDiagonals L Q A)⁻¹)^2-1) A
  change ‖((localDiagonals L Q A)⁻¹)^2-1‖ ≤ localMetricError L Q at h
  rw [Real.norm_eq_abs] at h
  exact h

noncomputable def localMetricMap (L Q : ℕ) : Space L →ₐ[ℂ] Space L :=
  exteriorScaling L (fun i => ((((modeFactor Q i.val)⁻¹)^2 : ℝ) : ℂ))

theorem localMetricMap_coordinate (L Q : ℕ) (x : Space L) (A : Finset (Fin (L+1))) :
    (occupationBasis L).repr (localMetricMap L Q x) A =
      ((((localDiagonals L Q A)⁻¹)^2 : ℝ) : ℂ) * (occupationBasis L).repr x A := by
  rw [localMetricMap,exteriorScaling_coordinate]
  have h : (∏ i ∈ A, ((((modeFactor Q i.val)⁻¹)^2 : ℝ) : ℂ)) =
      ((((localDiagonals L Q A)⁻¹)^2 : ℝ) : ℂ) := by
    simp only [← Complex.ofReal_prod]
    congr 1
    simp [localDiagonals,Finset.prod_pow,Finset.prod_inv_distrib]
  rw [h]

theorem localMetric_error_quadratic (L Q : ℕ) (x : Space L) :
    occupationNormSq L (localMetricMap L Q x - x) ≤
      (localMetricError L Q)^2 * occupationNormSq L x := by
  have he (A : Finset (Fin (L+1))) :
      (occupationBasis L).repr (localMetricMap L Q x - x) A =
        (((((localDiagonals L Q A)⁻¹)^2-1 : ℝ) : ℂ)) * (occupationBasis L).repr x A := by
    rw [map_sub,Finsupp.sub_apply,localMetricMap_coordinate]
    push_cast
    ring
  unfold occupationNormSq
  simp_rw [he]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A hA
  rw [norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hb : ‖((((localDiagonals L Q A)⁻¹)^2-1 : ℝ) : ℂ)‖ ≤ localMetricError L Q := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using localMetricError_bound L Q A
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

end Laughlin.Fock

end OAI
