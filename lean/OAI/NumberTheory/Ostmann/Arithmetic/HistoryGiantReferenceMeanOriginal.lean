import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanLaws

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryGiantReferenceMean
open Construction Conclusion Filter HistorySignedXiTransport HistorySignedDecode HistorySignedResidues
open HistorySupportReduction HistorySymbolicEncoding

theorem selected_prime_mean_zero_or_reference_eventually
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
      ∀(J : ℤ→ℤ→ℂ)(bc sc n : ℕ)(X tb td : ℝ),
      let a := sourceState C.sources T x s
      let b := sourceState C.sources T y t
      primeMean C.giant (sourceIntegrand d C.sources seed V outside l a b c e J bc sc X tb td C.giantCenter)=0 ∨
        ∃r : PrimeDraw C.giant,0 < primeWeight C.giant r ∧
          ∃(hs : (drawHistory C.sources seed V l a c (primeP C.giant) (primeQ C.giant) r).Supported V outside)
           (gs : (drawHistory C.sources seed V l b e (primeP C.giant) (primeQ C.giant) r).Supported V outside),
        primeMean C.giant (sourceIntegrand d C.sources seed V outside l a b c e J bc sc X tb td C.giantCenter)=
          primeMean C.giant (fun P Q => J P Q*referenceTerm d V outside
            (drawHistory C.sources seed V l a c (primeP C.giant) (primeQ C.giant) r)
            (drawHistory C.sources seed V l b e (primeP C.giant) (primeQ C.giant) r)
            hs gs n bc sc X tb td C.giantCenter P Q) := by
  filter_upwards [selected_zero_or_reference_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x y s t c e hx hy hc he outside hout J bc sc n X tb td
  have hh := hL E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he outside hout
    (PrimeDraw C.giant) (primeP C.giant) (primeQ C.giant) (primeWeight C.giant)
    (fun z => J (primeP C.giant z) (primeQ C.giant z)) bc sc n X tb td C.giantCenter
    (primeWeight_nonneg C.giant) (fun z _ => primeDraw_positive C.giant z)
  simpa only [weightedMean_prime,mul_assoc,primeMean_eq_weighted] using hh

theorem selected_mixed_mean_zero_or_reference_eventually
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
      ∀(J : ℤ→ℤ→ℂ)(bc sc n : ℕ)(X tb td : ℝ),
      let a := sourceState C.sources T x s
      let b := sourceState C.sources T y t
      mixedMean (C.giantCenter:ℝ) C.giant (sourceIntegrand d C.sources seed V outside l a b c e J bc sc X tb td C.giantCenter)=0 ∨
        ∃r : MixedDraw (C.giantCenter:ℝ) C.giant,0 < mixedWeight (C.giantCenter:ℝ) C.giant r ∧
          ∃(hs : (drawHistory C.sources seed V l a c (mixedP (C.giantCenter:ℝ) C.giant) (mixedQ (C.giantCenter:ℝ) C.giant) r).Supported V outside)
           (gs : (drawHistory C.sources seed V l b e (mixedP (C.giantCenter:ℝ) C.giant) (mixedQ (C.giantCenter:ℝ) C.giant) r).Supported V outside),
        mixedMean (C.giantCenter:ℝ) C.giant (sourceIntegrand d C.sources seed V outside l a b c e J bc sc X tb td C.giantCenter)=
          mixedMean (C.giantCenter:ℝ) C.giant (fun P Q => J P Q*referenceTerm d V outside
            (drawHistory C.sources seed V l a c (mixedP (C.giantCenter:ℝ) C.giant) (mixedQ (C.giantCenter:ℝ) C.giant) r)
            (drawHistory C.sources seed V l b e (mixedP (C.giantCenter:ℝ) C.giant) (mixedQ (C.giantCenter:ℝ) C.giant) r)
            hs gs n bc sc X tb td C.giantCenter P Q) := by
  filter_upwards [selected_zero_or_reference_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x y s t c e hx hy hc he outside hout J bc sc n X tb td
  have hh := hL E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he outside hout
    (MixedDraw (C.giantCenter:ℝ) C.giant) (mixedP (C.giantCenter:ℝ) C.giant) (mixedQ (C.giantCenter:ℝ) C.giant) (mixedWeight (C.giantCenter:ℝ) C.giant)
    (fun z => J (mixedP (C.giantCenter:ℝ) C.giant z) (mixedQ (C.giantCenter:ℝ) C.giant z)) bc sc n X tb td C.giantCenter
    (mixedWeight_nonneg (C.giantCenter:ℝ) C.giant) (fun z _ => mixedDraw_positive (C.giantCenter:ℝ) C.giant z)
  simpa only [weightedMean_mixed,mul_assoc,mixedMean_eq_weighted] using hh

end Ostmann.Arithmetic.HistoryGiantReferenceMean

end

end OAI
