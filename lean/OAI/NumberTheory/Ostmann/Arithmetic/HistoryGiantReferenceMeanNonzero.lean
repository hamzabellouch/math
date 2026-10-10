import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairGiantCoordinatesBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction HistorySignedXiTransport HistorySignedDecode HistorySignedResidues
open HistorySupportReduction HistorySymbolicEncoding

theorem zero_or_nonzero_reference {α : Type*} [Fintype α] (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (hout : ∀q∈outside,Nat.Prime q) (l : ℕ) (a b : State)
    (c e : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (P Q : α→ℤ) (w : α→ℝ) (J : α→ℂ) (bc sc n : ℕ) (X tb td G : ℝ)
    (hw : ∀i,0 ≤ w i) (hpos : ∀i,w i≠0→0<P i ∧ 0<Q i)
    (hlarge : ∀i,w i≠0→LargePrimes V (drawHistory sources seed V l a c P Q i))
    (glarge : ∀i,w i≠0→LargePrimes V (drawHistory sources seed V l b e P Q i)) :
    weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=0 ∨
      ∃r,0 < w r ∧ J r≠0 ∧
        supportedHistoryPairXi d V outside bc sc X tb td G
          (drawHistory sources seed V l a c P Q r) (drawHistory sources seed V l b e P Q r)≠0 ∧
        ∃(hs : (drawHistory sources seed V l a c P Q r).Supported V outside)
        (gs : (drawHistory sources seed V l b e P Q r).Supported V outside),
      weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=
        ∑i,(w i:ℂ)*J i*referenceTerm d V outside
          (drawHistory sources seed V l a c P Q r) (drawHistory sources seed V l b e P Q r)
          hs gs n bc sc X tb td G (P i) (Q i) := by
  by_cases hz : weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=0
  · exact Or.inl hz
  · obtain ⟨r,_,hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    have hXi := (mul_ne_zero_iff.mp hr).2
    have hwJ := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hr).1
    have hwr : w r≠0 := by exact_mod_cast hwJ.1
    have hsupport : (drawHistory sources seed V l a c P Q r).Supported V outside ∧
        (drawHistory sources seed V l b e P Q r).Supported V outside := by
      by_contra hh
      exact hXi (supportedHistoryPairXi_eq_zero_of_not d V outside bc sc X tb td G _ _ hh)
    exact Or.inr ⟨r,lt_of_le_of_ne (hw r) (Ne.symm hwr),hwJ.2,hXi,
      hsupport.1,hsupport.2,
      weightedMean_eq_reference d sources seed V outside hout l a b c e ha hb
        P Q w J bc sc n X tb td G hpos hlarge glarge r hsupport.1 hsupport.2⟩

theorem pairedRealXi_ne_zero_of_pairXi_ne_zero {l : ℕ} (d : Decomposition)
    (V : ℕ→ℕ) (outside : List ℕ) (bc sc : ℕ) (X tb td G : ℝ)
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hne : supportedHistoryPairXi d V outside bc sc X tb td G h k≠0) :
    HistoryPairSmoothXi.pairedRealXi bc sc X tb td G h k hs ks
      (HistoryPairGiantCoordinates.pairBackground h k)≠0 := by
  intro hz
  apply hne
  change HistoryPairSmoothXi.pairedRealXi bc sc X tb td G h k hs ks
    (fun i => (HistoryPairPattern.pairSample h k i:ℝ))=0 at hz
  simp only [supportedHistoryPairXi,dite_eq_left hs,dite_eq_left ks]
  rw [hz,mul_zero,zero_mul]

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
