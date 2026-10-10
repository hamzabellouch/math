import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction Conclusion Filter HistorySignedXiTransport HistorySignedDecode HistorySignedResidues
open HistorySupportReduction HistorySymbolicEncoding

def sourceState (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (s : ℤ) : State := ⟨s,0,0,assignedSlots sources T x⟩

theorem source_draw_largePrimes {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (x : SourceAssignment sources (Template.current seed l))
    (s : ℤ) (c : HistoryChoices sources seed V l) (P Q : α→ℤ) (i : α)
    (hx : (assignmentPrior sources (Template.current seed l)).mass x≠0)
    (hc : choicesMass sources seed V l c≠0)
    (hfreq : ∀j≤l,∀origin,(sources origin).AboveFrequency (V j)) :
    LargePrimes V (drawHistory sources seed V l (sourceState sources (Template.current seed l) x s) c P Q i) := by
  apply decoded_largePrimes sources seed V l _ c
  · exact Template.assignedSlots_matches _ _ _
  · exact assignedSlots_source_mass_ne_zero _ _ _ hx
  · exact hc
  · exact hfreq

theorem selected_zero_or_reference_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      let T := Template.current seed l
      ∀(x y : SourceAssignment C.sources T)(s t : ℤ)(c e : HistoryChoices C.sources seed V l),
      (assignmentPrior C.sources T).mass x≠0 → (assignmentPrior C.sources T).mass y≠0 →
      choicesMass C.sources seed V l c≠0 → choicesMass C.sources seed V l e≠0 →
      ∀outside : List ℕ,(∀q∈outside,Nat.Prime q) →
      ∀(α : Type) [Fintype α],∀(P Q : α→ℤ)(w : α→ℝ)(J : α→ℂ)(bc sc n : ℕ)(X tb td G : ℝ),
      (∀i,0 ≤ w i) → (∀i,w i≠0→0<P i ∧ 0<Q i) →
      let a := sourceState C.sources T x s
      let b := sourceState C.sources T y t
      weightedMean d C.sources seed V outside l a b c e P Q w J bc sc X tb td G=0 ∨
        ∃r,0 < w r ∧ ∃(hs : (drawHistory C.sources seed V l a c P Q r).Supported V outside)
          (gs : (drawHistory C.sources seed V l b e P Q r).Supported V outside),
        weightedMean d C.sources seed V outside l a b c e P Q w J bc sc X tb td G=
          ∑i,(w i:ℂ)*J i*referenceTerm d V outside
            (drawHistory C.sources seed V l a c P Q r) (drawHistory C.sources seed V l b e P Q r)
            hs gs n bc sc X tb td G (P i) (Q i) := by
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x y s t c e hx hy hc he outside hout α inst P Q w J bc sc n X tb td G hw hpos
  apply zero_or_reference d C.sources _ _ outside hout l _ _ c e
    (Template.assignedSlots_matches _ _ _) (Template.assignedSlots_matches _ _ _)
    P Q w J bc sc n X tb td G hw hpos
  · intro i _
    exact source_draw_largePrimes C.sources _ _ l x s c P Q i hx hc
      (fun j hj => (hL E C hG hcl hcu hb hd j (hj.trans hl)).2)
  · intro i _
    exact source_draw_largePrimes C.sources _ _ l y t e P Q i hy he
      (fun j hj => (hL E C hG hcl hcu hb hd j (hj.trans hl)).2)

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
