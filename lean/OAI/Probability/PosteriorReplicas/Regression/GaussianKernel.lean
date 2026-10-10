import OAI.Probability.PosteriorReplicas.Regression.GaussianDomination
import OAI.Probability.PosteriorReplicas.Regression.ReplicaKernel

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
section GaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_rows_kernel_bound {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℝ v)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1)
    (m : ℕ) (y : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) * ∏ j, φ (y j) := by
  let H : (Fin m → Fin n → ℝ) → ℝ≥0∞ :=
    fun z => ∏ j, φ (y j) * ∏ i, φ (y j - z j i)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have heq (A : Fin m → E) :
      (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫) =
      H (fun j i => ⟪v i, A j⟫) := by
    dsimp [H]
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
  simp_rw [heq]
  rw [← lintegral_map hH (by fun_prop)]
  calc
    _ ≤ ∫⁻ z, H z ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) •
        (volume : Measure (Fin m → Fin n → ℝ))) :=
      lintegral_mono' (gaussian_rows_pairings_le v hv m) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure]
      change _ * (∫⁻ z : Fin m → Fin n → ℝ, ∏ j, φ (y j) * ∏ i, φ (y j - z j i)) = _
      rw [lintegral_product_differences φ hφ hφ1]

lemma gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) := by
  have ht (A : Fin m → E) :
      (∫⁻ y : Fin m → ℝ, (∏ j, φ (y j - ⟪p, A j⟫)) *
        ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)) =
      ∫⁻ y : Fin m → ℝ, (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫) := by
    have he (y : Fin m → ℝ) (i : Fin n) (j : Fin m) :
        y j - ⟪p, A j⟫ - ⟪v i - p, A j⟫ = y j - ⟪v i, A j⟫ := by
      rw [inner_sub_left]
      ring
    simpa only [Pi.sub_apply, he] using
      lintegral_sub_right_eq_self
        (fun y : Fin m → ℝ => (∏ j, φ (y j)) * ∏ i, ∏ j, φ (y j - ⟪v i - p, A j⟫))
        (fun j => ⟪p, A j⟫)
  simp_rw [ht]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ ≤ ∫⁻ y : Fin m → ℝ,
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) *
        ∏ j, φ (y j) := lintegral_mono fun y =>
          gaussian_rows_kernel_bound (fun i => v i - p) hv φ hφ hφ1 m y
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), volume_pi,
        lintegral_fin_prod volume m (fun _ => φ) (fun _ => hφ)]
      simp [hφ1]
end GaussianKernel

end PosteriorRegression
end

end OAI
