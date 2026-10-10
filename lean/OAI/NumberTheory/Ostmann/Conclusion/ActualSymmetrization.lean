import OAI.NumberTheory.Ostmann.Conclusion.BulkPermutation
import OAI.NumberTheory.Ostmann.Conclusion.MaskedPermutation
import OAI.NumberTheory.Ostmann.Conclusion.PriorSymmetrization

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion
open Construction

abbrev AmplitudeSample (sources : SourceFamily) (seed : List SourceSlot)
    (giant spectator : PrimeSource) (m l : ℕ) :=
  (Fin m → spectator.Sample) × OuterSample sources (Template.current seed l) giant

def actualCoefficientRow (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (y : AmplitudeSample sources seed giant spectator m l) (s : AllowedFrequency V l) : ℂ :=
  actualCoefficient sources seed V X G g bins (spectatorList spectator y.1) l
    (outerState sources (Template.current seed l) giant y.2 s.val)

def actualSymmetrizedEnergy {Γ : Type*} [Fintype Γ]
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin) : ℝ :=
  (amplitudePrior sources seed giant spectator m l).mean (fun y =>
    ∑s : AllowedFrequency V l, ‖priorSymmetrizedCoefficient
      (fun γ => amplitudeSamplePermutation sources seed giant spectator m l (σ γ) (hσ γ))
      (actualCoefficientRow sources seed V giant spectator m X G g bins l) y s‖^2)

theorem actualAmplitude_symmetrized_bound {Γ : Type*} [Fintype Γ] [Nonempty Γ]
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ)
    (σ : Γ → Equiv.Perm (Fin (Template.current seed l).length))
    (hσ : ∀γ i, sources (Template.current seed l)[σ γ i].origin = sources (Template.current seed l)[i].origin) :
    ‖actualAmplitude sources seed V giant spectator m X G g giantTransform bins l‖^2 ≤
      actualRegularEnergy sources seed V giant spectator m g giantTransform l *
        actualSymmetrizedEnergy sources seed V giant spectator m X G g bins l σ hσ := by
  let R := fun (y : AmplitudeSample sources seed giant spectator m l) (s : AllowedFrequency V l) =>
    supportedRegularTransform g giantTransform (spectatorList spectator y.1)
      (outerState sources (Template.current seed l) giant y.2 s.val)
  have h := prior_correlation_symmetrized_bound (amplitudePrior sources seed giant spectator m l) R
    (actualCoefficientRow sources seed V giant spectator m X G g bins l)
    (fun γ => amplitudeSamplePermutation sources seed giant spectator m l (σ γ) (hσ γ))
    (fun γ => amplitudeSamplePermutation_mass sources seed giant spectator m l (σ γ) (hσ γ))
    (fun γ y s => supportedRegularTransform_amplitudeSamplePermutation sources seed giant spectator m l
      (σ γ) (hσ γ) g giantTransform y s.val)
  simpa only [R,actualCoefficientRow,actualRegularEnergy,actualSymmetrizedEnergy,amplitudePrior,
    FinitePrior.pair_cmean,supportedRegularTransform_mul_actualCoefficient,actualAmplitude] using h

theorem currentBulkAmplitude_symmetrized_bound (b k l m : ℕ)
    (bulk giant spectator : PrimeSource) (top : Fin 3 → PrimeSource) (comp : Fin k → Fin 2 → PrimeSource)
    (V : ℕ → ℕ) (X G : ℝ) (g giantTransform : (p : ℕ) → ZMod p → ℂ)
    (bins : List ℕ → State → ℝ) :
    let sources := initialSourceFamily b k bulk top comp
    let seed := Template.initial (2*b) k
    let σ := bulkPositionPermutation (Template.current seed l)
    let hσ := bulkPositionPermutation_source sources (Template.current seed l) bulk
      (current_bulk_source b k l bulk top comp)
    ‖actualAmplitude sources seed V giant spectator m X G g giantTransform bins l‖^2 ≤
      actualRegularEnergy sources seed V giant spectator m g giantTransform l *
        actualSymmetrizedEnergy sources seed V giant spectator m X G g bins l σ hσ := by
  exact actualAmplitude_symmetrized_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _

end Ostmann.Conclusion

end

end OAI
