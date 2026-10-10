import OAI.Combinatorics.ProgressionColoring.ConstructionModel
import OAI.Combinatorics.ProgressionColoring.OuterBalanced

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

/-- A concrete outer coloring, with its counted family of actual cyclic words.
The family is retained so that its membership proof can be used directly by the
subsequent progression dichotomy. -/
structure OuterChoice {k : ℕ} (s : Data k) (hk : 3 ≤ k) where
  words : Finset (Fin k → Label s hk)
  color : Label s hk → Bool
  word_mem : ∀ ad : Group s × Group s, fullLabelWord s hk ad ∈ words
  card_le : words.card ≤
    (16 * (3 * k ^ 2 *
      (uniformCount k + Fintype.card (mesh s hk).Label) + 1) ^ 6) ^
      (2 * dimension k)
  balanced : OuterBalanced (uniformCount k) (uniformCount_pos hk) (mesh s hk)
    (1 / (1000 * (dimension k : ℝ))) (lambda k) (cutoff k) words
    (Finset.Ioc (dimension k ^ 2) (2 * cutoff k)) color

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
