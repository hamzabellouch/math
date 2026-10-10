import OAI.Probability.InvariantIsing.Cavity.CavitySplitTestContinuity
import OAI.Probability.InvariantIsing.Cavity.CavityFullTail

namespace OAI

/-! The full-model cavity-spin observable can be evaluated using the
base overlap, since the discarded-site error is uniformly small. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

def cavityFullSpinInsertion {N depth : ℕ} (Φ : ℝ → ℝ) (site : Fin N)
    (σ : Fin 2 → Spin N × LabeledLeaf depth) : ℝ :=
  Φ (cavityReplicaOverlap σ) * (spinValue ((σ 0).1 site) * spinValue ((σ 1).1 site))

def cavitySplitSpinInsertion {N n depth : ℕ} (Φ : ℝ → ℝ) (site : Fin n)
    (σ : Fin 2 → Spin (N+n) × LabeledLeaf depth) : ℝ :=
  Φ (cavityTotalSpinOverlap ((cavitySpinSplit N n (σ 0).1).1,
    (cavitySpinSplit N n (σ 1).1).1)) *
      (spinValue ((σ 0).1 (Fin.natAdd N site)) * spinValue ((σ 1).1 (Fin.natAdd N site)))

theorem cavity_full_split_spin_test_tendsto {n m : ℕ}
    (N depth : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k+n))) [∀ k, IsProbabilityMeasure (μ k)]
    (T : (k : ℕ) → LabeledTree (depth k)) (eig : (k : ℕ) → Fin (N k+n) → ℝ)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k+n))) (u : ℕ → ℕ → ℝ)
    (Φ : ℝ →ᵇ ℝ) (site : Fin n) :
    Tendsto (fun k =>
      cavityFullTest (μ k) (T k) (eig k) (I k) (u k)
        (cavityFullSpinInsertion Φ (Fin.natAdd (N k) site)) -
      cavityFullTest (μ k) (T k) (eig k) (I k) (u k)
        (cavitySplitSpinInsertion Φ site)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_split_test_uniform (n := n) N hN hNlim Φ Φ.continuous
    (ε/2) (by positivity)] with k hk
  let F : SpecialOrthogonal (N k+n) → (Fin 2 → Spin (N k+n) × LabeledLeaf (depth k)) → ℝ :=
    fun _ => cavityFullSpinInsertion Φ (Fin.natAdd (N k) site)
  let G : SpecialOrthogonal (N k+n) → (Fin 2 → Spin (N k+n) × LabeledLeaf (depth k)) → ℝ :=
    fun _ => cavitySplitSpinInsertion Φ site
  have hmF : Measurable (Function.uncurry F) :=
    (measurable_of_countable (cavityFullSpinInsertion Φ (Fin.natAdd (N k) site))).comp measurable_snd
  have hmG : Measurable (Function.uncurry G) :=
    (measurable_of_countable (cavitySplitSpinInsertion (N := N k) Φ site)).comp measurable_snd
  have hFb U σ : |F U σ| ≤ ‖Φ‖ := by
    simpa only [F,cavityFullSpinInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityReplicaOverlap σ)
  have hGb U σ : |G U σ| ≤ ‖Φ‖ := by
    simpa only [G,cavitySplitSpinInsertion,abs_mul,abs_spinValue,one_mul,mul_one,Real.norm_eq_abs]
      using Φ.norm_coe_le_norm (cavityTotalSpinOverlap ((cavitySpinSplit (N k) n (σ 0).1).1,
        (cavitySpinSplit (N k) n (σ 1).1).1))
  have hd U σ : |F U σ-G U σ| ≤ ε/2 := by
    simpa only [F,G,cavityFullSpinInsertion,cavitySplitSpinInsertion,cavityReplicaOverlap,
      ← sub_mul,abs_mul,abs_spinValue,one_mul,mul_one] using (hk (σ 0).1 (σ 1).1).le
  have hh := cavityFullDisorderTest_abs_le (μ k) (T k) (eig k) (I k) (u k)
    (fun U σ => F U σ-G U σ) (hmF.sub hmG) (show 0 ≤ ε/2 by positivity) hd
  rw [cavityFullDisorderTest_sub (μ k) (T k) (eig k) (I k) (u k) F G hmF hmG
    (norm_nonneg Φ) hFb hGb] at hh
  rw [Real.dist_eq,sub_zero]
  exact hh.trans_lt (by linarith)

end InvariantIsing

end

end OAI
