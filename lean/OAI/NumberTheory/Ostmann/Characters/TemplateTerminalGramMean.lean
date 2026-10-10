import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalGram
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalParity

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels ParityActions OneSidedPhase
attribute [local instance] Classical.propDecidable

section
variable (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m≤width .word) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k (n+1)) width Q)
    (χ : PrimeCharacterData (schedule k (n+1)) width Q)
    (a : PrimeTranslationData (schedule k (n+1)) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (E : (schedule k (n+1)).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))

def terminalHistoryPairMean (σ ρ : Reassignments k n m)
    (h h' : SupportedHistory S (n+1) []) : ℂ :=
  (constituentPrimePrior (schedule k (n+1)) width E hE).cmean (fun x =>
    if h.val.1=h'.val.1 then
      conj (terminalHistoryTerm k (n+1) width ζ χ a B V extra mask X Δ W S
        (constituentAssignment (schedule k (n+1)) width
          (prefixConstituentPermutation k n width m hm σ) x) h)*
      terminalHistoryTerm k (n+1) width ζ χ a B V extra mask X Δ W S
        (constituentAssignment (schedule k (n+1)) width
          (prefixConstituentPermutation k n width m hm ρ) x) h'
    else 0)

theorem terminalParity_gram_eq_historyPairs (σ ρ : Reassignments k n m) :
    (constituentPrimePrior (schedule k (n+1)) width E hE).cmean (fun x =>
      ∑s : ↥(S []),conj (terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S σ x s)*
        terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S ρ x s)=
      ∑h : SupportedHistory S (n+1) [],∑h' : SupportedHistory S (n+1) [],
        terminalHistoryPairMean k n width m hm ζ χ a B V extra mask X Δ W S E hE σ ρ h h' := by
  simp only [terminalParityIntegrand,unitTerminalRoot_pair_eq,terminalHistoryPairMean,
    FinitePrior.cmean]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]

theorem terminalParity_gram_norm_le (σ ρ : Reassignments k n m) {e : ℝ}
    (hcancel : ∀h h',‖terminalHistoryPairMean k n width m hm ζ χ a B V extra mask X Δ W S E hE σ ρ h h'‖≤e) :
    ‖(constituentPrimePrior (schedule k (n+1)) width E hE).cmean (fun x =>
      ∑s : ↥(S []),conj (terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S σ x s)*
        terminalParityIntegrand k n width m hm ζ χ a B V extra mask X Δ W S ρ x s)‖ ≤
      (Fintype.card (SupportedHistory S (n+1) []) : ℝ)^2*e := by
  rw [terminalParity_gram_eq_historyPairs]
  calc
    _ ≤ ∑h : SupportedHistory S (n+1) [],‖∑h' : SupportedHistory S (n+1) [],
        terminalHistoryPairMean k n width m hm ζ χ a B V extra mask X Δ W S E hE σ ρ h h'‖ :=
      norm_sum_le _ _
    _ ≤ ∑h : SupportedHistory S (n+1) [],∑h' : SupportedHistory S (n+1) [],
        ‖terminalHistoryPairMean k n width m hm ζ χ a B V extra mask X Δ W S E hE σ ρ h h'‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑_h : SupportedHistory S (n+1) [],∑_h' : SupportedHistory S (n+1) [],e :=
      Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => hcancel h h'))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end
end Ostmann.Characters.Template

end

end OAI
