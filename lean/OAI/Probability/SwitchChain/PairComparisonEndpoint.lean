import OAI.Probability.SwitchChain.PairLocalComparison
import OAI.Probability.SwitchChain.PairSwitchComparison

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.PairResampling

theorem generator_energy_le_switchLaplacian_unconditional
    {n : ℕ} {d : Fin n → ℕ} (f : StateSpace n d) :
    ⟪f, generator n d f⟫ ≤
      2 * (n : ℝ) ^ 2 *
        ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
  exact generator_energy_le_switchLaplacian f
    (fluctuation_energy_le_pairSwitchLaplacian f)

theorem spectralGap_of_generator_square
    {n : ℕ} {d : Fin n → ℕ} (hn : 4 ≤ n) (hgraph : Graphical n d)
    (hsquare : ∀ f : StateSpace n d,
      ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  exact spectralGap_of_square_and_local_comparison hn hgraph hsquare
    fluctuation_energy_le_pairSwitchLaplacian

end Problem315.PairResampling

end

end OAI
