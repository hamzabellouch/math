import OAI.Probability.InvariantIsing.Cavity.CavitySplitOverlapTest
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTest
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFullTail

namespace OAI
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction
namespace InvariantIsing
theorem restricted_full_split_overlap_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ)
    (S : (k : ℕ) → Finset (Spin (N k+n))) (hS : ∀ k, (S k).Nonempty) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (T : (k : ℕ) → LabeledTree (depth k)) (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun k =>
      restrictedFullTest (S k) (hS k) (μ k) (T k) (eig k) (I k) (u k)
        (cavityFullOverlapInsertion Φ) -
      restrictedFullTest (S k) (hS k) (μ k) (T k) (eig k) (I k) (u k)
        (cavitySplitOverlapInsertion Φ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_split_test_uniform (n := n) N hN hNlim Φ Φ.continuous
    (ε/2) (by positivity)] with k hk
  let F : SpecialOrthogonal (N k+n) → (Fin 2 → Spin (N k+n) × LabeledLeaf (depth k)) → ℝ :=
    fun _ => cavityFullOverlapInsertion Φ
  let G : SpecialOrthogonal (N k+n) → (Fin 2 → Spin (N k+n) × LabeledLeaf (depth k)) → ℝ :=
    fun _ => cavitySplitOverlapInsertion Φ
  have hmF : Measurable (Function.uncurry F) :=
    (measurable_of_countable (cavityFullOverlapInsertion Φ)).comp measurable_snd
  have hmG : Measurable (Function.uncurry G) :=
    (measurable_of_countable (cavitySplitOverlapInsertion (N := N k) Φ)).comp measurable_snd
  have hFb U σ : |F U σ| ≤ ‖Φ‖ := by
    simpa only [F,cavityFullOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hGb U σ : |G U σ| ≤ ‖Φ‖ := by
    simpa only [G,cavitySplitOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n (σ 0).1).1,
        (cavitySpinSplit (N k) n (σ 1).1).1))
  have hd U σ : |F U σ-G U σ| ≤ ε/2 := by
    simpa only [F,G,cavityFullOverlapInsertion,cavitySplitOverlapInsertion,cavityReplicaOverlap,
      ← sub_mul,abs_mul,abs_spinValue,one_mul,mul_one] using (hk (σ 0).1 (σ 1).1).le
  have hh := restrictedCavityFullDisorderTest_abs_le (S k) (hS k) (μ k) (T k) (eig k) (I k) (u k)
    (fun U σ => F U σ-G U σ) (hmF.sub hmG) (show 0 ≤ ε/2 by positivity) hd
  rw [restrictedCavityFullDisorderTest_sub (S k) (hS k) (μ k) (T k) (eig k) (I k) (u k) F G hmF hmG
    (norm_nonneg Φ) hFb hGb] at hh
  rw [Real.dist_eq,sub_zero]
  exact hh.trans_lt (by linarith)

theorem restricted_full_split_tree_overlap_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ)
    (S : (k : ℕ) → Finset (Spin (N k+n))) (hS : ∀ k, (S k).Nonempty) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (θ : (k : ℕ) → Measure (LabeledTree (depth k))) [∀ k, IsProbabilityMeasure (θ k)]
    (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun k =>
      (∫ T, restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k)
        (cavityFullOverlapInsertion Φ) ∂θ k) -
      ∫ T, restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k)
        (cavitySplitOverlapInsertion Φ) ∂θ k) atTop (𝓝 0) := by
  let O := fun k (T : LabeledTree (depth k)) =>
    restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k)
      (cavityFullOverlapInsertion Φ)
  let C := fun k (T : LabeledTree (depth k)) =>
    restrictedFullTest (S k) (hS k) (μ k) T (eig k) (I k) (u k) (cavitySplitOverlapInsertion Φ)
  have hlim := cavity_average_zero_of_all_selections θ (fun k T => O k T-C k T)
    (fun T => restricted_full_split_overlap_test_tendsto N depth S hS hN hNlim μ T eig I u Φ)
  apply hlim.congr'
  filter_upwards [] with k
  have hO : Integrable (O k) (θ k) := integrable_of_measurable_abs_le
    (measurable_restrictedFullTest_tree (S k) (hS k) _ _ _ _ _) (fun T =>
      restrictedCavityFullDisorderTest_abs_le (S k) (hS k) (μ k) T (eig k) (I k) (u k) (fun _ => cavityFullOverlapInsertion Φ)
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavityFullOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)))
  have hC : Integrable (C k) (θ k) := integrable_of_measurable_abs_le
    (measurable_restrictedFullTest_tree (S k) (hS k) _ _ _ _ _) (fun T =>
      restrictedCavityFullDisorderTest_abs_le (S k) (hS k) (μ k) T (eig k) (I k) (u k) (fun _ => cavitySplitOverlapInsertion (N := N k) Φ)
        ((measurable_of_countable _).comp measurable_snd) (norm_nonneg Φ)
        (fun U σ => by
          simpa only [cavitySplitOverlapInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
            using Φ.norm_coe_le_norm (cavityTotalSpinOverlap
              ((cavitySpinSplit (N k) n (σ 0).1).1,(cavitySpinSplit (N k) n (σ 1).1).1))))
  exact integral_sub hO hC


end InvariantIsing

end

end OAI
