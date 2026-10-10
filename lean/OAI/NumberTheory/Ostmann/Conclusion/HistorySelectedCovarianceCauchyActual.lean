import OAI.NumberTheory.Ostmann.Conclusion.HistorySelectedCovarianceCauchyBasic

namespace OAI

noncomputable section
namespace Ostmann.Conclusion
open Construction

theorem actualPermutationCovariance_self_eq_energy {Γ : Type*}
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin)
    (a : Γ) :
    actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a a =
      actualCoefficientEnergy sources seed V giant spectator m X G g bins l := by
  exact prior_permuted_self_covariance
    (amplitudePrior sources seed giant spectator m l)
    (actualCoefficientRow sources seed V giant spectator m X G g bins l)
    (fun γ => amplitudeSamplePermutation sources seed giant spectator m l (σ γ) (hσ γ))
    (fun γ => amplitudeSamplePermutation_mass sources seed giant spectator m l (σ γ) (hσ γ)) a

theorem actualPermutationCovariance_le_energy {Γ : Type*}
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin)
    (a b : Γ) :
    actualPermutationCovariance sources seed V giant spectator m X G g bins l σ hσ a b ≤
      actualCoefficientEnergy sources seed V giant spectator m X G g bins l := by
  exact prior_permuted_covariance_le_energy
    (amplitudePrior sources seed giant spectator m l)
    (actualCoefficientRow sources seed V giant spectator m X G g bins l)
    (fun γ => amplitudeSamplePermutation sources seed giant spectator m l (σ γ) (hσ γ))
    (fun γ => amplitudeSamplePermutation_mass sources seed giant spectator m l (σ γ) (hσ γ)) a b

end Ostmann.Conclusion

end

end OAI
