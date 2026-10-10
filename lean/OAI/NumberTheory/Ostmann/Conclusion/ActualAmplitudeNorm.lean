import OAI.NumberTheory.Ostmann.Conclusion.PermutationSymmetrization
import OAI.NumberTheory.Ostmann.Construction.CoefficientSupport

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Conclusion
open Construction

def supportedRegularTransform (g giant : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (a : State) : ℂ := by
  classical
  exact if a.Coprime outside ∧ a.frequency≠0 then regularTransform g giant outside a else 0

def amplitudePrior (sources : SourceFamily) (seed : List SourceSlot)
    (giant spectator : PrimeSource) (m l : ℕ) :
    FinitePrior ((Fin m → spectator.Sample) × OuterSample sources (Template.current seed l) giant) :=
  (spectatorPrior spectator m).pair (outerPrior sources (Template.current seed l) giant)

def actualRegularEnergy (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (l : ℕ) : ℝ :=
  (amplitudePrior sources seed giant spectator m l).mean (fun y =>
    ∑s : AllowedFrequency V l, ‖supportedRegularTransform g giantTransform
      (spectatorList spectator y.1) (outerState sources (Template.current seed l) giant y.2 s.val)‖^2)

def actualCoefficientEnergy (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ) : ℝ :=
  (amplitudePrior sources seed giant spectator m l).mean (fun y =>
    ∑s : AllowedFrequency V l, ‖actualCoefficient sources seed V X G g bins
      (spectatorList spectator y.1) l (outerState sources (Template.current seed l) giant y.2 s.val)‖^2)

theorem supportedRegularTransform_mul_actualCoefficient (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (X G : ℝ) (g giant : (p : ℕ) → ZMod p → ℂ)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (l : ℕ) (a : State) :
    supportedRegularTransform g giant outside a * actualCoefficient sources seed V X G g bins outside l a =
      regularTransform g giant outside a * actualCoefficient sources seed V X G g bins outside l a := by
  classical
  by_cases hA : actualCoefficient sources seed V X G g bins outside l a=0
  · simp only [hA,mul_zero]
  obtain ⟨c,hm,hs,hw⟩ := canonicalCoefficient_ne_zero_witness sources seed V outside
    (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
    Ostmann.smoothPartition G l a hA
  have hc : a.Coprime outside := by
    simpa only [decodeHistory_root] using History.supported_root_coprime hs
  have hf : a.frequency≠0 := by
    simpa only [decodeHistory_root] using History.supported_root_frequency_ne_zero hs
  unfold supportedRegularTransform
  rw [ite_eq_left ⟨hc,hf⟩]

theorem prior_correlation_cauchy_schwarz {J S : Type*} [Fintype J] [Fintype S]
    (μ : FinitePrior J) (R A : J → S → ℂ) :
    ‖μ.cmean (fun j => ∑s,R j s*A j s)‖^2 ≤
      μ.mean (fun j => ∑s,‖R j s‖^2)*μ.mean (fun j => ∑s,‖A j s‖^2) := by
  have h := weighted_cauchy_schwarz (fun y : J×S => μ.mass y.1)
    (fun y => μ.mass_nonneg y.1) (fun y => R y.1 y.2) (fun y => A y.1 y.2)
  simpa only [FinitePrior.cmean,FinitePrior.mean,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc] using h

theorem actualAmplitude_cauchy_schwarz (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ) (l : ℕ) :
    ‖actualAmplitude sources seed V giant spectator m X G g giantTransform bins l‖^2 ≤
      actualRegularEnergy sources seed V giant spectator m g giantTransform l *
        actualCoefficientEnergy sources seed V giant spectator m X G g bins l := by
  let R := fun (y : (Fin m → spectator.Sample) × OuterSample sources (Template.current seed l) giant)
    (s : AllowedFrequency V l) => supportedRegularTransform g giantTransform
    (spectatorList spectator y.1) (outerState sources (Template.current seed l) giant y.2 s.val)
  let A := fun (y : (Fin m → spectator.Sample) × OuterSample sources (Template.current seed l) giant)
    (s : AllowedFrequency V l) => actualCoefficient sources seed V X G g bins
    (spectatorList spectator y.1) l (outerState sources (Template.current seed l) giant y.2 s.val)
  have h := prior_correlation_cauchy_schwarz (amplitudePrior sources seed giant spectator m l) R A
  simpa only [R,A,actualRegularEnergy,actualCoefficientEnergy,amplitudePrior,FinitePrior.pair_cmean,
    supportedRegularTransform_mul_actualCoefficient,actualAmplitude] using h

end Ostmann.Conclusion

end

end OAI
