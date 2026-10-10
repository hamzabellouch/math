import OAI.Probability.SwitchChain.DisjointAlgebra
import OAI.Probability.SwitchChain.PairGeneratorSquare

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem disjoint_sum_nonnegative_of_pair_bounds {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d)
    (hinteraction : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b‖ ^ 2 - ‖R a b‖ ^ 2 - ‖R b a‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hrows : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b‖ ^ 2 else 0) :
    0 ≤ ∑ a ∈ pairs n, ∑ b ∈ pairs n,
      if Disjoint a b then ⟪fluctuation n d a f, fluctuation n d b f⟫ else 0 := by
  exact Problem315.disjoint_inner_sum_nonnegative (pairs n) Disjoint
    (fun h => h.symm) (fun a => fluctuation n d a f) g R hinteraction hrows

theorem generator_square_of_triples_and_pair_bounds {n : ℕ} {d : Fin n → ℕ}
    (hn : 3 ≤ n) (f : StateSpace n d)
    (g R : Finset (Fin n) → Finset (Fin n) → StateSpace n d)
    (htriple : ∀ T : Finset (Fin n), T.card = 3 →
      ⟪f, tripleGenerator n d T f⟫ ≤
        ⟪tripleGenerator n d T f, tripleGenerator n d T f⟫)
    (hinteraction : ∀ a ∈ pairs n, ∀ b ∈ pairs n, Disjoint a b →
      2 * ‖g a b‖ ^ 2 - ‖R a b‖ ^ 2 - ‖R b a‖ ^ 2 ≤
        2 * ⟪fluctuation n d a f, fluctuation n d b f⟫)
    (hrows : ∀ a ∈ pairs n,
      (∑ b ∈ pairs n, if Disjoint a b then ‖R a b‖ ^ 2 else 0) ≤
        ∑ b ∈ pairs n, if Disjoint a b then ‖g a b‖ ^ 2 else 0) :
    ⟪f, generator n d f⟫ ≤ ⟪generator n d f, generator n d f⟫ := by
  exact generator_square_of_local hn f htriple
    (disjoint_sum_nonnegative_of_pair_bounds f g R hinteraction hrows)

end Problem315.PairResampling

end

end OAI
