import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordAbsorption
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordStatistic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceWord
open Filter InitialCharacterScale Construction Preliminaries

theorem family_source_word_eventually (k : ℕ) {α γ δ cA : ℝ} (β : ℝ)
    (hα : 0<α) (hγ : 0<γ) (hδ : 0<δ) (hcA : 0<cA) :
    ∀ᶠ L : ℝ in atTop,∀u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      ∀{d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)}
        (F : HigherBiasSourceFamily d Q E δ)
        (bulk top : Finset (PrimeUpTo Q))
        (hb : 0<primeShellMass bulk) (ht : 0<primeShellMass top) (H : Finset ℤ),
      (∀p∈bulk,Real.log (p.val:ℝ) ≤ Real.exp (u-γ*L)) →
      (∀p∈top,Real.exp u ≤ Real.log (p.val:ℝ) ∧
        Real.log (p.val:ℝ) ≤ Real.exp 1*Real.exp u) →
      (∀n∈H,δ/2 ≤ ((primeShellPrior bulk hb).cmean (fun p=>F.test p (n:ZMod p.val))).re ∧
        δ/2 ≤ ((primeShellPrior top ht).cmean (fun p=>F.test p (n:ZMod p.val))).re) →
      cA*Real.sqrt (higherSourceX k u:ℝ)/(Real.log (higherSourceX k u:ℝ))^3 ≤ (H.card:ℝ) →
      ∃J : ℤ,∃H₀ : Finset ℤ,H₀⊆H ∧
        (9/10:ℝ)*Real.exp u ≤ (J:ℝ) ∧ (J:ℝ) ≤ 4*Real.exp u ∧
        Real.sqrt (higherSourceX k u:ℝ)*
          Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)) ≤ (H₀.card:ℝ) ∧
        ∀n∈H₀,Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)) ≤
          ‖initialCharacterMean (roleShells bulk top (wordSize k L))
            (roleShells_mass_pos hb ht (wordSize k L))
            (fun _=>familyCharacter F) (fun _=>familyCenter F) (fun _=>familyPhase F)
            (binIndicator J) n‖ := by
  filter_upwards [source_word_eventually k β hα hγ (show 0<δ/2 by positivity) hcA]
    with L hL
  intro u hu hU d Q E F bulk top hb ht H hbulk htop hmean hH
  have hb' : ∀p,(primeShellPrior bulk hb).mass p≠0 →
      Real.log (p.val:ℝ) ≤ Real.exp (u-γ*L) := by
    intro p hp
    apply hbulk p
    by_contra hn
    exact hp (by rw [primeShellPrior_mass,ite_eq_right hn,zero_div])
  have ht' : ∀p,(primeShellPrior top ht).mass p≠0 →
      Real.exp u ≤ Real.log (p.val:ℝ) ∧ Real.log (p.val:ℝ) ≤ Real.exp 1*Real.exp u := by
    intro p hp
    apply htop p
    by_contra hn
    exact hp (by rw [primeShellPrior_mass,ite_eq_right hn,zero_div])
  obtain ⟨J,H₀,hsub,hlo,hhi,hcard,hgood⟩ := hL u hu hU
    (primeShellPrior bulk hb) (primeShellPrior top ht)
    (fun p n=>F.test p (n:ZMod p.val)) H hb' ht' hmean hH
  refine ⟨J,H₀,hsub,hlo,hhi,hcard,?_⟩
  intro n hn
  simpa only [family_binMean_eq_initialCharacterMean F hb ht] using hgood n hn

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
