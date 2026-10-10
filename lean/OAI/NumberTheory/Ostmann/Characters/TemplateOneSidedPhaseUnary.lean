import OAI.NumberTheory.Ostmann.Characters.AnchorInteraction
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseQuotient

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def historyUnaryAt (k j : ℕ) (width : Role → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (q : ℕ) : ℂ :=
  if hq : q.Prime then
    @actualHistoryUnary k width q ⟨hq⟩ (χ q) j s t i
  else 0

@[simp] theorem historyUnaryAt_prime (k j : ℕ) (width : Role → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (q : ℕ) [hq : Fact q.Prime] :
    historyUnaryAt k j width χ s t i q=actualHistoryUnary k width (χ q) j s t i := by
  simp only [historyUnaryAt,dite_eq_left hq.out]

def quotientUnary (k j : ℕ) (width : Role → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (q : ℕ) : ℂ :=
  historyUnaryAt k j width χ s t (σ i) q / historyUnaryAt k j width χ s u (ρ i) q

theorem norm_quotientUnary (k j : ℕ) (width : Role → ℕ)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (q : ℕ) [Fact q.Prime]
    (hχ : χ q≠1) (ht : HistoryFrequencyUnits q j s t) (hu : HistoryFrequencyUnits q j s u) :
    ‖quotientUnary k j width χ σ ρ s t u i q‖=1 := by
  simp only [quotientUnary,historyUnaryAt_prime,norm_div,
    norm_actualHistoryUnary k width (χ q) hχ j s t ht,
    norm_actualHistoryUnary k width (χ q) hχ j s u hu,div_self one_ne_zero]

def exposedCharacter {q : ℕ} (χ : MulChar (ZMod q) ℂ) (positive : Bool) : MulChar (ZMod q) ℂ :=
  if positive then χ^2 else (χ^2)⁻¹

theorem exposedCharacter_ne_one {q : ℕ} (χ : MulChar (ZMod q) ℂ)
    (hχ : 2<orderOf χ) (positive : Bool) : exposedCharacter χ positive≠1 := by
  have hh := square_or_inverse_ne_one χ hχ
  cases positive
  · exact hh.2
  · exact hh.1

theorem actualHistoryPhase_pair_eq_quotient (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,χ (p i)≠1)
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (hu : ∀i,HistoryFrequencyUnits (p i) j s u) :
    actualHistoryPhase k j width (fun i=>p (σ.symm i))
        (fun i=>χ (p (σ.symm i))) (fun i=>a (p (σ.symm i))) s t *
      conj (actualHistoryPhase k j width (fun i=>p (ρ.symm i))
        (fun i=>χ (p (ρ.symm i))) (fun i=>a (p (ρ.symm i))) s u) =
      primeGraphPhase
        (fun i h=>permutedGraph (constituentGraph k j width) σ i h-
          permutedGraph (constituentGraph k j width) ρ i h) p (fun i=>χ (p i))
        (fun i=>quotientUnary k j width χ σ ρ s t u i (p i)) := by
  have hc' : Pairwise (fun i h=>(p (ρ.symm i)).Coprime (p (ρ.symm h))) :=
    fun i h hih=>hc (ρ.symm.injective.ne hih)
  have hn := norm_actualHistoryPhase k j width (fun i=>p (ρ.symm i)) hc'
    (fun i=>χ (p (ρ.symm i))) (fun i=>hχ (ρ.symm i))
    (fun i=>a (p (ρ.symm i))) s u (fun i=>hu (ρ.symm i))
  rw [←Complex.inv_eq_conj hn,←div_eq_mul_inv,actualHistoryPhase_quotient k j width σ ρ p hc (fun i=>χ (p i)) (fun i=>a (p i)) s t u]
  simp only [quotientUnary,historyUnaryAt_prime]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
