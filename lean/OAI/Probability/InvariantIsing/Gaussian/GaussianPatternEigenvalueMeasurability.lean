import OAI.Probability.InvariantIsing.Spectral.HermitianEigenvalueLimits

namespace OAI

/-! Measurability of the actual sorted Gaussian Gram spectrum, including repeated zero roots. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology Matrix.Norms.L2Operator
namespace InvariantIsing

lemma continuous_hermitian_eigenvalues₀ {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    {N : ℕ} (A : X → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hc : Continuous A) : Continuous (fun x => (hA x).eigenvalues₀) := by
  apply SeqContinuous.continuous
  intro x p hp
  exact hermitian_eigenvalues₀_tendsto (fun n => A (x n)) (fun n => hA (x n)) (A p) (hA p)
    ((hc.tendsto p).comp hp)

lemma continuous_hermitian_eigenvalues {X : Type*} [TopologicalSpace X] [SequentialSpace X]
    {N : ℕ} (A : X → Matrix (Fin N) (Fin N) ℝ) (hA : ∀ x, (A x).IsHermitian)
    (hc : Continuous A) : Continuous (fun x => (hA x).eigenvalues) := by
  apply continuous_pi
  intro i
  exact (continuous_apply _).comp (continuous_hermitian_eigenvalues₀ A hA hc)

lemma continuous_gaussianPatternCoupling (N m : ℕ) (c : ℝ) :
    Continuous (gaussianPatternCoupling (N := N) (m := m) c) := by
  unfold gaussianPatternCoupling gaussianPatternArray
  fun_prop

theorem continuous_gaussianPatternEigenvalues (N m : ℕ) :
    Continuous (gaussianPatternEigenvalues (N := N) (m := m)) := by
  unfold gaussianPatternEigenvalues
  exact continuous_hermitian_eigenvalues (gaussianPatternCoupling 1)
    (gaussianPatternCoupling_isHermitian 1) (continuous_gaussianPatternCoupling N m 1)

theorem measurable_gaussianPatternEigenvalues (N m : ℕ) :
    Measurable (gaussianPatternEigenvalues (N := N) (m := m)) :=
  (continuous_gaussianPatternEigenvalues N m).measurable

end InvariantIsing

end

end OAI
