import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalUnitRoot

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem root_pair_sum_eq (j : ℕ) (S : List Bool → Finset ℤ) (p : List Bool)
    (F G : SupportedHistory S j p → ℂ) :
    (∑s : ↥(S p),conj (∑h,if h.val.1=s.val then F h else 0)*
      (∑h,if h.val.1=s.val then G h else 0))=
    ∑h,∑h',if h.val.1=h'.val.1 then conj (F h)*G h' else 0 := by
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h' hh'
  have hs : h.val.1∈S p :=
    mem_labels_range S h.property (root_mem_labels j p h.val.1 h.val.2)
  let s : ↥(S p) := ⟨h.val.1,hs⟩
  rw [Finset.sum_eq_single s]
  · by_cases he : h.val.1=h'.val.1 <;> simp [s,he,eq_comm]
  · intro s' hs' hne
    have hn : h.val.1≠s'.val := fun he => hne (Subtype.ext he.symm)
    simp only [ite_eq_right hn,map_zero,zero_mul]
  · simp

section
variable (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)

def terminalHistoryTerm (x : (schedule k j).Constituent width → PrimeUpTo Q)
    (h : SupportedHistory S j []) : ℂ :=
  if samplePrimeSupport (schedule k j) width x then
    retainedHistoryWeight k B V extra mask X Δ W j h.val.1
      (constituentSampleState (schedule k j) width x) h.val.2 *
      unitHistoryPhase k j width ζ χ a x h.val.1 h.val.2
  else 0

theorem unitTerminalRootIntegrand_eq_histories
    (x : (schedule k j).Constituent width → PrimeUpTo Q) (s : ↥(S [])) :
    unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S x s=
      ∑h : SupportedHistory S j [],if h.val.1=s.val then
        terminalHistoryTerm k j width ζ χ a B V extra mask X Δ W S x h else 0 := by
  by_cases hx : samplePrimeSupport (schedule k j) width x
  · simp only [unitTerminalRootIntegrand,terminalRootIntegrand,terminalHistoryTerm,
      ite_eq_left hx,historyRootSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    split_ifs
    · unfold unitHistoryPhase
      ring
    · exact mul_zero _
  · simp only [unitTerminalRootIntegrand,terminalRootIntegrand,terminalHistoryTerm,
      ite_eq_right hx,mul_zero,ite_self,Finset.sum_const_zero]

theorem unitTerminalRoot_pair_eq
    (x y : (schedule k j).Constituent width → PrimeUpTo Q) :
    (∑s : ↥(S []),conj (unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S x s)*
      unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S y s)=
      ∑h : SupportedHistory S j [],∑h' : SupportedHistory S j [],
        if h.val.1=h'.val.1 then
          conj (terminalHistoryTerm k j width ζ χ a B V extra mask X Δ W S x h)*
            terminalHistoryTerm k j width ζ χ a B V extra mask X Δ W S y h' else 0 := by
  simp only [unitTerminalRootIntegrand_eq_histories]
  exact root_pair_sum_eq j S [] _ _

end
end Ostmann.Characters.Template

end

end OAI
