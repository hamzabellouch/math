import OAI.Probability.SwitchChain.ProposalLaplacian
import OAI.Probability.SwitchChain.OrthogonalPairResampling
import OAI.Probability.SwitchChain.PairPoincare

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

theorem generator_energy_le_switchLaplacian {n : Nat} {d : Fin n → Nat}
    (f : StateSpace n d)
    (hlocal : ∀ a ∈ pairs n,
      ⟪f, fluctuation n d a f⟫ ≤ (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G) :
    ⟪f, generator n d f⟫ ≤
      2 * (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
  calc
    ⟪f, generator n d f⟫ = ∑ a ∈ pairs n, ⟪f, fluctuation n d a f⟫ := by
      rw [generator_apply, inner_sum]
    _ ≤ ∑ a ∈ pairs n, (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G :=
      Finset.sum_le_sum hlocal
    _ = 2 * (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      simp only [pairs, sum_pairSwitchLaplacian]
      have hsum : (∑ G : GraphState n d,
          f G * (2 * switchLaplacian n d (fun H => f H) G)) =
          2 * ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro G hG
        ring
      rw [hsum]
      ring

theorem spectralGap_of_square_and_local_comparison {n : Nat} {d : Fin n → Nat}
    (hn : 4 ≤ n) (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫)
    (hlocal : ∀ (f : StateSpace n d) a, a ∈ pairs n →
      ⟪f, fluctuation n d a f⟫ ≤ (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ)^2 * (Nat.choose n 4 : ℝ))) := by
  apply switch_chain_gap_of_laplacian_poincare hn
  intro f
  have hcomparison := generator_energy_le_switchLaplacian
    (WithLp.toLp 2 f) (hlocal (WithLp.toLp 2 f))
  calc
    uniformVariance n d f ≤
        ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ /
          (stateCount n d : ℝ) := uniformVariance_le_generator hgraph hsquare f
    _ ≤ (2 * (n : ℝ)^2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d f G) /
          (stateCount n d : ℝ) :=
      div_le_div_of_nonneg_right hcomparison (Nat.cast_nonneg _)
    _ = 2 * (n : ℝ)^2 * uniformInner n d f (switchLaplacian n d f) := by
      unfold uniformInner uniformAverage allGraphStates
      ring

end Problem315.PairResampling

end

end OAI
