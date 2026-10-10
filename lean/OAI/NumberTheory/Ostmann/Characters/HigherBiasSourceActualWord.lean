import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Filter

theorem exists_actual_selected_word_sources (d : Decomposition) (α β c δ : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ ρ γ c₀ : ℝ,0 < ρ ∧ 0 < γ ∧ 0 < c₀ ∧
      ∃ M h : ℕ,2 ≤ M ∧ ∃ Kmin : ℝ,0 < Kmin ∧
      ∀ K0 : ℕ,Kmin ≤ (K0:ℝ) → ∀ᶠ L : ℝ in atTop,
      ∀ E : Finset ℕ,
        (∀ p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
        c*L ≤ harmonicPrimeMass E → (∀ p∈E,δ ≤ higherPrimeBias d p) →
        ∃ j : Fin (h+1),Nonempty (SelectedWordSource d E δ L (K0*M^j.val) α β ρ γ c₀) := by
  classical
  obtain ⟨ρ,γ,c₀,hρ,hγ,hc₀,M,h,hM,Kmin,hKmin,hselect⟩ :=
    higherSource_rich_shell_selection α β c hα hαβ hc
  refine ⟨ρ,γ,c₀,hρ,hγ,hc₀,M,h,hM,Kmin,hKmin,?_⟩
  intro K0 hK
  have hwords : ∀ᶠ L : ℝ in atTop,∀ j : Fin (h+1),
      ∀ u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      ∀ E : Finset ℕ,(∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p)) →
      (∀p∈E,δ ≤ higherPrimeBias d p) →
      ∀ B w s U : ℝ,B+w ≤ u-γ*L → s+1 ≤ u+1 →
      c₀ ≤ harmonicIntervalMass E B (B+w) →
      c₀ ≤ harmonicIntervalMass E s (s+1) →
      c₀ ≤ harmonicIntervalMass E u (u+1) →
      let X := higherSourceX (K0*M^j.val) u
      let E' := boundedPrimeSet (Preliminaries.collisionScale 10 X) E
      let base := fun i : Fin 3 => boundedInterval E' (![B,s,u] i) (![B+w,s+1,u+1] i)
      let G := testedShellFamily E' base c₀ U (Real.log X) (K0*M^j.val)
      ∃ hm : ∀ i,0 < primeShellMass (G i),
      ∃ F : HigherBiasSourceFamily d (Preliminaries.collisionScale 10 X) E' δ,
      ∃ hb : 0 < primeShellMass (base 0),∃ ht : 0 < primeShellMass (base 2),
      ∃ J : ℤ,∃ H : Finset ℤ,
        (∀ n∈H,∃ a∈Preliminaries.upperWindow d.A X,(a:ℤ)=n) ∧
        (9/10:ℝ)*Real.exp u ≤ (J:ℝ) ∧ (J:ℝ) ≤ 4*Real.exp u ∧
        Real.sqrt X*Real.exp (-HigherBiasSourceWord.selectionCost β (δ/2)*
          (InitialCharacterScale.wordSize (K0*M^j.val) L:ℝ)) ≤ H.card ∧
        (∀ n∈H,Real.exp (-HigherBiasSourceWord.selectionCost β (δ/2)*
          (InitialCharacterScale.wordSize (K0*M^j.val) L:ℝ)) ≤
          ‖initialCharacterMean (HigherBiasSourceWord.roleShells (base 0) (base 2)
              (InitialCharacterScale.wordSize (K0*M^j.val) L))
            (HigherBiasSourceWord.roleShells_mass_pos hb ht _)
            (fun _=>HigherBiasSourceWord.familyCharacter F)
            (fun _=>HigherBiasSourceWord.familyCenter F)
            (fun _=>HigherBiasSourceWord.familyPhase F)
            (HigherBiasSourceWord.binIndicator J) n‖) ∧
        ∀ n∈H,∀ i,δ/2 ≤
          ((primeShellPrior (G i) (hm i)).cmean (fun p=>F.test p (n:ZMod p.val))).re := by
    apply Filter.eventually_all.mpr
    intro j
    exact eventually_higherSource_selected_word d δ c₀ hδ hc₀ (K0*M^j.val) α β γ hα hγ
  have hmass : ∀ᶠ L : ℝ in atTop,c₀ ≤ ρ*L :=
    (Filter.tendsto_id.const_mul_atTop hρ).eventually_ge_atTop c₀
  filter_upwards [hselect K0 hK,hwords,hmass,eventually_ge_atTop (0:ℝ)] with L hs hw hm hL
  intro E hE hmass hbias
  obtain ⟨j,w,A,B,D,s,U,u,hk,hwlo,hwhi,hA,hAB,hBD,hDe,hmB,hsA,hse,hsm,
    hDU,hUe,hUu,hue,hul,huu,hum,hBg,hsg,hrich⟩ := hs E hE hmass
  let loc : SourceLocations E L (K0*M^j.val) α β ρ γ c₀ :=
    ⟨w,A,B,D,s,U,u,hk,hwlo,hwhi,hA,hAB,hBD,hDe,hmB,hsA,hse,hsm,
      hDU,hUe,hUu,hue,hul,huu,hum,hBg,hsg,hrich⟩
  obtain ⟨hm,F,hb,ht,J,H,hH,hJl,hJu,hcard,hword,hmeans⟩ :=
    hw j u hul huu E (fun p hp=>(hE p hp).1) (fun p hp=>(hE p hp).2.1) hbias
      B w s U hBg (by nlinarith) (hm.trans hmB) hsm hum
  exact ⟨j,⟨⟨loc,F,hm,hb,ht,J,H,hH,hJl,hJu,hcard,hword,hmeans⟩⟩⟩

end Ostmann.Characters.HigherBiasSource

end

end OAI
