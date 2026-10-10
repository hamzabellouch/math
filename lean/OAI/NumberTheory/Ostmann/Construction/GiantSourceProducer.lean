import OAI.NumberTheory.Ostmann.Construction.GiantPriorProducer
import OAI.NumberTheory.Ostmann.Supply.NonsparseSupply

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

theorem actual_positive_giant_prior : ∃ δ : ℝ, 0<δ ∧
    ∀ d : Decomposition, ∀ r : ℝ, 4≤r →
      ∀ᶠ L : ℝ in atTop,
        ∃ G : ℝ, ∃ c : ℤ, ∃ P : Finset ℕ, ∃ hZ : 0<logCellMass c ∅,
          P⊆Supply.nonsparsePrimes d δ L ∧
          Real.exp ((1/20:ℝ)*L)≤G ∧
          G+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
          G-2<(c:ℝ) ∧ (c:ℝ)<G+favorableBlockWidth L+2 ∧
          (∀p∈P,G≤Real.log p ∧ Real.log p<G+favorableBlockWidth L) ∧
          δ/(320*Real.sqrt 2)<(logCellPrior c ∅ hZ).mean
            (fun p => if (p:ℕ)∈P then giantEmpiricalMean d (giantWindowScale r G L) p else 0) := by
  obtain ⟨δ,hδ,hsupply⟩ := Supply.nonsparse_supply
  refine ⟨δ,hδ,?_⟩
  intro d r hr
  filter_upwards [hsupply d,exists_positive_giant_prior d hδ r hr] with L hm hprior
  exact hprior hm

end Ostmann.Construction

end

end OAI
