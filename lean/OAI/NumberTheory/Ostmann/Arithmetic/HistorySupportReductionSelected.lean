import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReduction
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionSources
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open Erdos970

noncomputable section
open Filter
open scoped Classical
namespace Ostmann.Arithmetic.HistorySupportReduction
open Construction Conclusion

theorem selected_decoded_largePrimes_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,∀(x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant)
        (s : ℤ)(c : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l),
      (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant).mass x≠0 →
      choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l c≠0 →
      LargePrimes (frequencyBound Bs BD Bz k L)
        (decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l
          (outerState C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant x s) c) := by
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl x s c hx hc
  have hx' : C.giant.law.mass x.1*(C.giant.law.mass x.2.1*
      (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x.2.2)≠0 := hx
  have hmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).2
  apply decoded_largePrimes C.sources _ _ l _ c
  · exact Template.assignedSlots_matches _ _ _
  · exact assignedSlots_source_mass_ne_zero _ _ _ hmass
  · exact hc
  · intro j hj
    exact (hL E C hG hcl hcu hb hd j (hj.trans hl)).2

theorem selected_supported_term_eq_reduced_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,∀(x : OuterSample C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant)
        (s : ℤ)(c : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l)
        (outside : List ℕ)(base : State → ℂ)(φ : ℝ → ℝ)(G : ℝ),
      let T := Template.current (Template.initial (2*(bulkSize k L/2)) k) l
      let H := decodeHistory C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l
        (outerState C.sources T C.giant x s) c
      ((outerPrior C.sources T C.giant).mass x:ℂ)*
        (choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l c:ℂ)*
        H.supportedWeight (frequencyBound Bs BD Bz k L) outside base φ G =
      ((outerPrior C.sources T C.giant).mass x:ℂ)*
        (choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l c:ℂ)*
        (if H.root.Coprime outside ∧ Reduced (frequencyBound Bs BD Bz k L) outside H then H.weight base φ G else 0) := by
  filter_upwards [selected_decoded_largePrimes_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl x s c outside base φ G
  dsimp only
  by_cases hx : (outerPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l) C.giant).mass x=0
  · simp only [hx,Complex.ofReal_zero,zero_mul]
  by_cases hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) l c=0
  · simp only [hc,Complex.ofReal_zero,mul_zero,zero_mul]
  rw [supportedWeight_eq_reduced _ _ _ _ _ _ (hL E C hG hcl hcu hb hd l hl x s c hx hc)]

end Ostmann.Arithmetic.HistorySupportReduction

end

end OAI
