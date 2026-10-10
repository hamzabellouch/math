import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesXiSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction HistorySignedXiTransport HistorySignedDecode HistorySignedResidues
open HistorySupportReduction HistorySymbolicEncoding

def drawHistory {α : Type*} (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (i : α) : History l :=
  decodeHistory sources seed V l (giantState a (P i) (Q i)) c

def weightedMean {α : Type*} [Fintype α] (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (w : α→ℝ) (J : α→ℂ) (bc sc : ℕ) (X tb td G : ℝ) : ℂ :=
  ∑i,(w i:ℂ)*J i*supportedHistoryPairXi d V outside bc sc X tb td G
    (drawHistory sources seed V l a c P Q i) (drawHistory sources seed V l b e P Q i)

def referenceTerm (d : Decomposition) (V : ℕ→ℕ) (outside : List ℕ)
    {l : ℕ} (h g : History l) (hs : h.Supported V outside) (gs : g.Supported V outside)
    (n bc sc : ℕ) (X tb td G : ℝ) (P Q : ℤ) : ℂ :=
  if Nat.Coprime P.natAbs Q.natAbs then
    ((h.compensationProduct:ℂ)*(g.compensationProduct:ℂ))*
      actualRealXi bc sc X tb td G outside h g hs gs (signedGiantSample h P Q) (signedGiantSample g P Q)*
      liftedResidueTest (residueTransform d) V outside h g (comparisonModulus h g outside n)
        (pairModulus_dvd_comparisonModulus h g outside n) (P,Q)
  else 0

lemma giantState_twice (a : State) (P Q P' Q' : ℤ) :
    giantState (giantState a P Q) P' Q'=giantState a P' Q' := rfl

theorem weightedMean_zero_of_no_reference {α : Type*} [Fintype α] (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (P Q : α→ℤ) (w : α→ℝ) (J : α→ℂ) (bc sc : ℕ) (X tb td G : ℝ)
    (hw : ∀i,0 ≤ w i)
    (hn : ¬∃i,0 < w i ∧ (drawHistory sources seed V l a c P Q i).Supported V outside ∧
      (drawHistory sources seed V l b e P Q i).Supported V outside) :
    weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : w i=0
  · simp only [hi,Complex.ofReal_zero,zero_mul]
  · have hnot : ¬((drawHistory sources seed V l a c P Q i).Supported V outside ∧
        (drawHistory sources seed V l b e P Q i).Supported V outside) :=
      fun hh => hn ⟨i,lt_of_le_of_ne (hw i) (Ne.symm hi),hh⟩
    rw [supportedHistoryPairXi_eq_zero_of_not d V outside bc sc X tb td G _ _ hnot,mul_zero]

theorem weightedMean_eq_reference {α : Type*} [Fintype α] (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (hout : ∀q∈outside,Nat.Prime q) (l : ℕ) (a b : State)
    (c e : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (P Q : α→ℤ) (w : α→ℝ) (J : α→ℂ) (bc sc n : ℕ) (X tb td G : ℝ)
    (hpos : ∀i,w i≠0→0<P i ∧ 0<Q i)
    (hlarge : ∀i,w i≠0→LargePrimes V (drawHistory sources seed V l a c P Q i))
    (glarge : ∀i,w i≠0→LargePrimes V (drawHistory sources seed V l b e P Q i))
    (r : α) (hs : (drawHistory sources seed V l a c P Q r).Supported V outside)
    (gs : (drawHistory sources seed V l b e P Q r).Supported V outside) :
    weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=
      ∑i,(w i:ℂ)*J i*referenceTerm d V outside
        (drawHistory sources seed V l a c P Q r) (drawHistory sources seed V l b e P Q r)
        hs gs n bc sc X tb td G (P i) (Q i) := by
  let h := drawHistory sources seed V l a c P Q r
  let g := drawHistory sources seed V l b e P Q r
  let : NeZero (pairModulus
      (decodeHistory sources seed V l (giantState a (P r) (Q r)) c)
      (decodeHistory sources seed V l (giantState b (P r) (Q r)) e) outside) :=
    ⟨(pairModulus_pos h g hs gs (fun q hq => (hout q hq).pos)).ne'⟩
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : w i=0
  · simp only [hi,Complex.ofReal_zero,zero_mul]
  · have heq := supportedHistoryPairXi_eq_residueTest d sources seed V outside l
      (giantState a (P r) (Q r)) (giantState b (P r) (Q r)) c e ha hb
      (P i) (Q i) (hpos i hi).1 (hpos i hi).2 hs gs
      (hlarge i hi) (glarge i hi) (comparisonModulus h g outside n)
      (pairModulus_dvd_comparisonModulus h g outside n) bc sc X tb td G
    exact congrArg (fun z : ℂ => (w i:ℂ)*J i*z) heq

theorem zero_or_reference {α : Type*} [Fintype α] (d : Decomposition)
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
      ∃r,0 < w r ∧ ∃(hs : (drawHistory sources seed V l a c P Q r).Supported V outside)
        (gs : (drawHistory sources seed V l b e P Q r).Supported V outside),
      weightedMean d sources seed V outside l a b c e P Q w J bc sc X tb td G=
        ∑i,(w i:ℂ)*J i*referenceTerm d V outside
          (drawHistory sources seed V l a c P Q r) (drawHistory sources seed V l b e P Q r)
          hs gs n bc sc X tb td G (P i) (Q i) := by
  by_cases hh : ∃i,0 < w i ∧ (drawHistory sources seed V l a c P Q i).Supported V outside ∧
      (drawHistory sources seed V l b e P Q i).Supported V outside
  · obtain ⟨r,hr,hs,gs⟩ := hh
    exact Or.inr ⟨r,hr,hs,gs,weightedMean_eq_reference d sources seed V outside hout l a b c e ha hb
      P Q w J bc sc n X tb td G hpos hlarge glarge r hs gs⟩
  · exact Or.inl (weightedMean_zero_of_no_reference d sources seed V outside l a b c e P Q w J
      bc sc X tb td G hw hh)

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
