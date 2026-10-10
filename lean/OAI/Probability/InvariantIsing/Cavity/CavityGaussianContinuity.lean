import OAI.Probability.InvariantIsing.Cavity.CavityGaussianImage
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace OAI

/-! Weak continuity of the finite Gaussian marks in their covariance,
including singular limiting covariance matrices. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace InvariantIsing

variable {a : Type*} [Fintype a] [DecidableEq a]

lemma cavity_sqrt_tendsto (S : ℕ → Matrix a a ℝ)
    (S₀ : Matrix a a ℝ) (hS : ∀ n, (S n).PosSemidef)
    (hS₀ : S₀.PosSemidef) (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => CFC.sqrt (S n)) atTop (𝓝 (CFC.sqrt S₀)) := by
  have hw : Tendsto S atTop (𝓝[{A : Matrix a a ℝ | 0 ≤ A}] S₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hS n).nonneg)⟩
  have hc := (CFC.continuousOn_sqrt (A := Matrix a a ℝ)).continuousWithinAt
    hS₀.nonneg
  exact hc.tendsto.comp hw

lemma cavity_matrix_action_continuous (x : EuclideanSpace ℝ a) :
    Continuous (fun A : Matrix a a ℝ => A.toEuclideanLin x) := by
  change Continuous (fun A : Matrix a a ℝ =>
    WithLp.toLp 2 (fun i => ∑ j, A i j * x j))
  fun_prop

theorem cavity_multivariateGaussian_integral_tendsto 
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀))
    (F : EuclideanSpace ℝ a →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F x ∂multivariateGaussian 0 (S n)) atTop
      (𝓝 (∫ x, F x ∂multivariateGaussian 0 S₀)) := by
  have hrep (A : Matrix a a ℝ) :
      (∫ x, F x ∂multivariateGaussian 0 A) =
      ∫ x : EuclideanSpace ℝ a, F ((CFC.sqrt A).toEuclideanLin x) ∂stdGaussian _ := by
    rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop)]
    simp only [zero_add]
    rfl
  simp_rw [hrep]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.comp
      (CFC.sqrt (S n)).toEuclideanLin.continuous_of_finiteDimensional).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun x => F.norm_coe_le_norm _)
  · exact ae_of_all _ (fun x => F.continuous.tendsto _ |>.comp
      ((cavity_matrix_action_continuous x).tendsto _ |>.comp
        (cavity_sqrt_tendsto S S₀ hS hS₀ hlim)))

theorem cavity_multivariateGaussian_weak_tendsto 
    (S : ℕ → Matrix a a ℝ) (S₀ : Matrix a a ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hS₀ : S₀.PosSemidef)
    (hlim : Tendsto S atTop (𝓝 S₀)) :
    Tendsto (fun n => (⟨multivariateGaussian 0 (S n), inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ a))) atTop
      (nhds (X := ProbabilityMeasure (EuclideanSpace ℝ a))
        ⟨multivariateGaussian 0 S₀, inferInstance⟩) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  exact cavity_multivariateGaussian_integral_tendsto S S₀ hS hS₀ hlim

end InvariantIsing

end

end OAI
