import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTypicalShells
import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWord

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Preliminaries Construction HigherBiasSource HigherBiasSourceWord InitialCharacterScale Filter
open scoped BigOperators

theorem eventually_higherSource_selected_word (d : Decomposition)
    (δ c₀ : ℝ) (hδ : 0 < δ) (hc₀ : 0 < c₀) :
    ∀ (k : ℕ) (α β γ : ℝ),0 < α → 0 < γ →
      ∀ᶠ L : ℝ in atTop,∀ u : ℝ,α*L-1 ≤ u → u ≤ β*L →
      ∀ E : Finset ℕ,(∀ p∈E,p.Prime) →
      (∀ p∈E,α*L ≤ Real.log (Real.log p)) →
      (∀ p∈E,δ ≤ higherPrimeBias d p) →
      ∀ B w s U : ℝ,B+w ≤ u-γ*L → s+1 ≤ u+1 →
      c₀ ≤ harmonicIntervalMass E B (B+w) →
      c₀ ≤ harmonicIntervalMass E s (s+1) →
      c₀ ≤ harmonicIntervalMass E u (u+1) →
      let X := higherSourceX k u
      let E' := boundedPrimeSet (collisionScale 10 X) E
      let base := fun i : Fin 3 => boundedInterval E' (![B,s,u] i) (![B+w,s+1,u+1] i)
      let G := testedShellFamily E' base c₀ U (Real.log X) k
      ∃ hm : ∀ i,0 < primeShellMass (G i),
      ∃ F : HigherBiasSourceFamily d (collisionScale 10 X) E' δ,
      ∃ hb : 0 < primeShellMass (base 0),∃ ht : 0 < primeShellMass (base 2),
      ∃ J : ℤ,∃ H : Finset ℤ,
        (∀ n∈H,∃ a∈upperWindow d.A X,(a:ℤ)=n) ∧
        (9/10:ℝ)*Real.exp u ≤ (J:ℝ) ∧ (J:ℝ) ≤ 4*Real.exp u ∧
        Real.sqrt X*Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)) ≤ H.card ∧
        (∀ n∈H,Real.exp (-selectionCost β (δ/2)*(wordSize k L:ℝ)) ≤
          ‖initialCharacterMean (roleShells (base 0) (base 2) (wordSize k L))
            (roleShells_mass_pos hb ht (wordSize k L))
            (fun _=>familyCharacter F) (fun _=>familyCenter F) (fun _=>familyPhase F)
            (binIndicator J) n‖) ∧
        ∀ n∈H,∀ i,δ/2 ≤
          ((primeShellPrior (G i) (hm i)).cmean (fun p => F.test p (n:ZMod p.val))).re := by
  classical
  obtain ⟨cA,hcA,htyp⟩ := eventually_higherSource_actual_typical_shells d δ c₀ hδ hc₀
  intro k α β γ hα hγ
  filter_upwards [htyp k α β hα,
    family_source_word_eventually k β hα hγ hδ hcA,eventually_ge_atTop (0:ℝ)]
    with L ht hw hL
  intro u hul huu E hprime hband hbias B w s U hB hs hBm hsm hum
  dsimp only
  let X := higherSourceX k u
  let E' := boundedPrimeSet (collisionScale 10 X) E
  let base := fun i : Fin 3 => boundedInterval E' (![B,s,u] i) (![B+w,s+1,u+1] i)
  let G := testedShellFamily E' base c₀ U (Real.log X) k
  obtain ⟨hm,F,H,hH,hcard,hmean⟩ := ht u hul huu E hprime hband hbias
    ![B,s,u] ![B+w,s+1,u+1] (by
      intro i
      fin_cases i
      · change B+w ≤ u+1
        nlinarith
      · change s+1 ≤ u+1
        exact hs
      · exact le_rfl)
    (by
      intro i
      fin_cases i
      · exact hBm
      · exact hsm
      · exact hum) U
  have hg (i : Fin 3) : G (firstTestIndex k i)=base i := testedShellFamily_first _ _ _ _ _ _ _
  have hb : 0 < primeShellMass (base 0) := by rw [← hg 0]; exact hm _
  have htop : 0 < primeShellMass (base 2) := by rw [← hg 2]; exact hm _
  let HI : Finset ℤ := H.image (fun a:ℕ => (a:ℤ))
  have hHIcard : HI.card=H.card := Finset.card_image_of_injective _ Int.ofNat_injective
  have hHImean : ∀ n∈HI,∀ i,δ/2 ≤
      ((primeShellPrior (G i) (hm i)).cmean (fun p=>F.test p (n:ZMod p.val))).re := by
    intro n hn i
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
    simpa only [Int.cast_natCast] using hmean a ha i
  obtain ⟨J,H0,hsub,hJl,hJu,hcard0,hword⟩ := hw u hul huu F (base 0) (base 2) hb htop HI
    (by
      intro p hp
      exact (boundedInterval_log_bounds E' B (B+w) p hp).2.trans (Real.exp_le_exp.mpr hB))
    (by
      intro p hp
      have hh := boundedInterval_log_bounds E' u (u+1) p hp
      exact ⟨hh.1.le,by simpa only [Real.exp_add,mul_comm] using hh.2⟩)
    (by
      intro n hn
      constructor
      · have hh := hHImean n hn (firstTestIndex k 0)
        simpa only [hg 0] using hh
      · have hh := hHImean n hn (firstTestIndex k 2)
        simpa only [hg 2] using hh)
    (by simpa only [hHIcard] using hcard)
  refine ⟨hm,F,hb,htop,J,H0,?_,hJl,hJu,hcard0,hword,?_⟩
  · intro n hn
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp (hsub hn)
    exact ⟨a,hH ha,he⟩
  · intro n hn i
    exact hHImean n (hsub hn) i

end Ostmann.Characters

end

end OAI
