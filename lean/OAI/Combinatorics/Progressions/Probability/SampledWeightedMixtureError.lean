import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem finiteProbability_mixture_error_bound {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Ω) (error weight : Ω → ℂ) (e : Ω → ℝ) {D : ℝ}
    (herror : ∀ t, ‖error t‖ ≤ e t * D) (hweight : ∀ t, ‖weight t‖ ≤ 1) :
    ‖law.complexMean (fun t => weight t * error t)‖ ≤ law.mean e * D := by
  apply (law.norm_complexMean_le_mean_norm _).trans
  calc
    law.mean (fun t => ‖weight t * error t‖) ≤ law.mean (fun t => e t * D) :=
      law.mean_mono (fun t => by
        rw [norm_mul]
        exact ((mul_le_mul_of_nonneg_right (hweight t) (norm_nonneg _)).trans_eq
          (one_mul _)).trans (herror t))
    _ = law.mean (fun t => D * e t) := congrArg law.mean (funext (fun t => mul_comm _ _))
    _ = D * law.mean e := law.mean_const_mul D e
    _ = law.mean e * D := mul_comm _ _

theorem selectedResidue_weightedMixture_error {Ω K X : Type*}
    [Fintype Ω] [Fintype K] [Fintype X]
    (law : FiniteProbabilityWeights Ω) (e : Ω → ℝ) (he : ∀ t, 0 ≤ e t)
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (error weight : (K × X → ℤ) → Ω → ℂ) (D : (K × X → ℤ) → ℝ)
    (herror : ∀ z t, ‖error z t‖ ≤ e t * D z)
    (hweight : ∀ z t, ‖weight z t‖ ≤ 1) {M : ℝ}
    (hD : selectedResidueDensityMass stride cells V D ≤ M) :
    selectedResidueDensityMass stride cells V
      (fun z => ‖law.complexMean (fun t => weight z t * error z t)‖) ≤ law.mean e * M ∧
    ∀ φ : (K × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
        (law.complexMean (fun t => weight z t * error z t) * φ z)‖ ≤ law.mean e * M := by
  exact selectedResidue_weightedError_test_le stride cells V hV hZ
    (fun z => law.complexMean (fun t => weight z t * error z t)) D
    (law.mean_nonneg he)
    (fun z => finiteProbability_mixture_error_bound law (error z) (weight z) e (herror z) (hweight z)) hD

end Erdos3.BooleanCubeKernel

end

end OAI
