import OAI.Probability.InvariantIsing.Cavity.ConsecutiveProductSpin
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullSpinAverage
import OAI.Probability.InvariantIsing.Cavity.CavityOverlapWeightedTest

namespace OAI

/-! The averaged last-block spin insertion is the full weighted-overlap
observable, including the original random cascade tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem consecutive_product_tree_spin_identity {n K m depth : ℕ}
    (hn : 0 < n) (hK : 2 ≤ K) (C : Finset (Spin n)) (hC : C.Nonempty)
    (μ : Measure (SpecialOrthogonal (K*n+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (θ : Measure (LabeledTree depth)) [IsProbabilityMeasure θ]
    (eig : Fin (K*n+n) → ℝ) (I : Fin m → Finset (Fin (K*n+n)))
    (u : ℕ → ℝ) (hu : ∀ k, |u k| ≤ 2) (Φ : ℝ →ᵇ ℝ) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, ∫ T, restrictedFullTest
      (cavityProductSlice (consecutiveBlockConstraint n K C) C)
      (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
      μ T eig I u (cavityFullSpinInsertion Φ (Fin.natAdd (K*n) i)) ∂θ =
    ∫ T, restrictedFullTest
      (cavityProductSlice (consecutiveBlockConstraint n K C) C)
      (cavityProductSlice_nonempty _ (consecutiveBlockConstraint_nonempty C hC) C hC)
      μ T eig I u (cavityFullOverlapInsertion (cavityOverlapWeightedTest Φ)) ∂θ := by
  rw [← restricted_full_tree_spin_average]
  apply integral_congr_ae
  filter_upwards [] with T
  have he := consecutive_product_spin_identity hn hK C hC μ T eig I u hu Φ (Fin.last K)
  simp only [consecutiveProductSite_last] at he
  unfold restrictedFullTest
  rw [he]
  congr 1
  funext U σ
  exact (cavityOverlapWeightedTest_eq Φ
    (abs_le.mp (abs_cavityTotalSpinOverlap_le ((σ 0).1,(σ 1).1)))).symm

end InvariantIsing

end

end OAI
