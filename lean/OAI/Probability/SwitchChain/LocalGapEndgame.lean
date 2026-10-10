import OAI.Probability.SwitchChain.PairGeneratorSquare
import OAI.Probability.SwitchChain.PairSwitchComparison
import OAI.Probability.SwitchChain.PairLocalComparison

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem spectralGap_of_triples_disjoint_and_local_comparison
    {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n) (hgraph : Graphical n d)
    (htriple : ∀ (f : StateSpace n d) (T : Finset (Fin n)), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : StateSpace n d,
      0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0)
    (hlocal : ∀ (f : StateSpace n d) a, a ∈ pairs n →
      ⟪f, fluctuation n d a f⟫ ≤ (n : ℝ) ^ 2 *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  apply spectralGap_of_square_and_local_comparison hn hgraph _ hlocal
  intro f
  exact generator_square_of_local (by omega) f (htriple f) (hdisjoint f)

theorem spectralGap_of_triples_and_disjoint
    {n : Nat} {d : Fin n → Nat} (hn : 4 ≤ n) (hgraph : Graphical n d)
    (htriple : ∀ (f : StateSpace n d) (T : Finset (Fin n)), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hdisjoint : ∀ f : StateSpace n d,
      0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
        if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0) :
    hasSpectralGapAtLeast n d
      ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) :=
  spectralGap_of_triples_disjoint_and_local_comparison hn hgraph htriple hdisjoint
    fluctuation_energy_le_pairSwitchLaplacian

end Problem315.PairResampling

end

end OAI
