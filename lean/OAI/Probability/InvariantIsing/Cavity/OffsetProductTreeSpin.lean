import OAI.Probability.InvariantIsing.Cavity.OffsetProductSpin

namespace OAI

/-! Averaging the prefix error over the original random cascade tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace InvariantIsing

theorem offset_product_tree_spin_error {n K r m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (R : Finset (Spin r)) (hR : R.Nonempty)
    (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (r+K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (eig : Fin (r+K*n+n) → ℝ) (I : Fin m → Finset (Fin (r+K*n+n)))
    (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2) (Φ : ℝ →ᵇ ℝ) :
    |(n : ℝ)⁻¹ * ∑ i : Fin n, ∫ T, restrictedFullTest
      (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i)) ∂θ -
      ∫ T, restrictedFullTest (cavityProductSlice (offsetBlockConstraint K R C) C)
      (cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC)
      μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ)) ∂θ| ≤
      ‖Φ‖*(2*(r : ℝ)/(r+K*n+n)) := by
  let S := cavityProductSlice (offsetBlockConstraint K R C) C
  have hS : S.Nonempty := cavityProductSlice_nonempty _ (offsetBlockConstraint_nonempty R hR C hC) C hC
  have hspin (i : Fin n) : Integrable (fun T => restrictedFullTest S hS μ T eig I u
      (cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i))) θ := by
    apply integrable_of_measurable_abs_le (measurable_restrictedFullTest_tree S hS μ eig I u _)
    intro T
    change |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i))| ≤ ‖Φ‖
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u
      (fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (r+K*n) i))
      ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
    intro U σ
    simpa only [cavityFullSpinInsertion,abs_mul,abs_spinValue,mul_one,one_mul,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  let F := fun (T : LabeledTree depth) => restrictedFullTest S hS μ T eig I u (fun σ => Φ (cavityReplicaOverlap σ) *
    ((n : ℝ)⁻¹ * ∑ i : Fin n, spinValue ((σ 0).1 (Fin.natAdd (r+K*n) i)) *
      spinValue ((σ 1).1 (Fin.natAdd (r+K*n) i))))
  let G := fun (T : LabeledTree depth) => restrictedFullTest S hS μ T eig I u
    (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))
  have hF : Integrable F θ := by
    simp only [F, restricted_full_spin_average]
    exact (integrable_finsetSum _ fun i _ => hspin i).const_mul _
  have hG : Integrable G θ := by
    apply integrable_of_measurable_abs_le (measurable_restrictedFullTest_tree S hS μ eig I u _)
    intro T
    change |restrictedCavityFullDisorderTest S hS μ T eig I u
      (fun _ => cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))| ≤ ‖cavityOverlapWeightedTest Φ‖
    apply restrictedCavityFullDisorderTest_abs_le S hS μ T eig I u
      (fun _ => cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ))
      ((measurable_of_countable _).comp measurable_snd) (norm_nonneg (cavityOverlapWeightedTest Φ))
    intro U σ
    simpa only [cavityFullOverlapInsertion,Real.norm_eq_abs] using
      (cavityOverlapWeightedTest Φ).norm_coe_le_norm (cavityReplicaOverlap σ)
  rw [← restricted_full_tree_spin_average]
  change |(∫ T, F T ∂θ)-(∫ T, G T ∂θ)| ≤ _
  rw [← integral_sub hF hG]
  have hh := norm_integral_le_of_norm_le_const (μ := θ) (f := fun T => F T-G T)
    (C := ‖Φ‖*(2*(r : ℝ)/(r+K*n+n))) (ae_of_all _ fun T => by
      simpa only [Real.norm_eq_abs] using offset_product_spin_error hn hK R hR C hC μ T eig I u hu Φ)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end InvariantIsing

end

end OAI
