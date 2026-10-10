import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineRequest
import OAI.Combinatorics.MatchingCount.Complexity.OnlineSampleCost

namespace OAI

namespace MatchingFPRAS.NumericBounds
open Polynomial TreeTyped

variable {A B : Type}
def Bound (f m : A→ℕ) : Prop := ∃ p : Polynomial ℕ,∀ x,f x≤p.eval (m x)
lemma self (m : A→ℕ) : Bound m m := ⟨X,fun _=>by simp⟩
lemma of_le {f m : A→ℕ} (h : ∀ x,f x ≤ m x) : Bound f m := ⟨X,fun x=>by simpa using h x⟩
lemma const (n : ℕ) (m : A→ℕ) : Bound (fun _=>n) m := ⟨C n,fun _=>by simp⟩
lemma mono {f g m : A→ℕ} (hf : Bound f m) (h : ∀ x,g x≤f x) : Bound g m := by
  obtain ⟨p,hp⟩:=hf;exact ⟨p,fun x=>(h x).trans (hp x)⟩
lemma add {f g m : A→ℕ} (hf : Bound f m) (hg : Bound g m) : Bound (fun x=>f x+g x) m := by
  obtain ⟨p,hp⟩:=hf;obtain ⟨q,hq⟩:=hg
  exact ⟨p+q,fun x=>by simpa using Nat.add_le_add (hp x) (hq x)⟩
lemma mul {f g m : A→ℕ} (hf : Bound f m) (hg : Bound g m) : Bound (fun x=>f x*g x) m := by
  obtain ⟨p,hp⟩:=hf;obtain ⟨q,hq⟩:=hg
  exact ⟨p*q,fun x=>by simpa using Nat.mul_le_mul (hp x) (hq x)⟩
lemma pow {f m : A→ℕ} (hf : Bound f m) (n : ℕ) : Bound (fun x=>f x^n) m := by
  obtain ⟨p,hp⟩:=hf
  exact ⟨p^n,fun x=>by simpa using Nat.pow_le_pow_left (hp x) n⟩
lemma clog_le (n : ℕ) : Nat.clog 2 n≤n := by
  apply Nat.clog_le_of_le_pow
  exact (Nat.lt_two_pow_self (n:=n)).le
lemma clog {f m : A→ℕ} (hf : Bound f m) : Bound (fun x=>Nat.clog 2 (f x)) m :=
  mono hf (fun _=>clog_le _)
lemma comp {f : A→B} {m : A→ℕ} {n g : B→ℕ} (hg : Bound g n) (hf : Bound (n ∘ f) m) :
    Bound (g ∘ f) m := by
  obtain ⟨p,hp⟩:=hg;obtain ⟨q,hq⟩:=hf
  exact ⟨p.comp q,fun x=>by simpa using (hp (f x)).trans (polynomial_eval_monotone p (hq x))⟩
lemma weight [Codec A] [Codec B] {f : A→B} {F : Realizer f} {m : A→ℕ}
    (hF : WorkBound F m) : Bound (fun x=>TreeTyped.weight (f x)) m := by
  obtain ⟨p,hp⟩:=hF
  exact ⟨p,fun x=>(Nat.le_add_left _ _).trans (hp x)⟩
lemma length [Codec A] [Codec B] {f : A→List B} {F : Realizer f} {m : A→ℕ}
    (hF : WorkBound F m) : Bound (fun x=>(f x).length) m :=
  mono (weight hF) (fun _=>list_length_le_weight _)
end MatchingFPRAS.NumericBounds

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Polynomial NumericBounds Transport ExecutableSource

def precisionNorm (x : PrecisionData) : ℕ :=
  x.1.1.1.1+x.1.1.1.2+x.1.1.2.1+x.1.1.2.2+x.1.2+x.2.1+x.2.2
lemma bound_plan : Bound (fun x : PrecisionData=>
    (precisionPlan x).1.1.1+(precisionPlan x).1.1.2+(precisionPlan x).1.2+(precisionPlan x).2) precisionNorm := by
  have hN : Bound (fun x : PrecisionData=>x.1.1.1.1) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hD : Bound (fun x : PrecisionData=>x.1.1.1.2) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hK : Bound (fun x : PrecisionData=>x.1.1.2.1) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hT : Bound (fun x : PrecisionData=>x.1.1.2.2) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hm : Bound (fun x : PrecisionData=>x.1.2) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hE : Bound (fun x : PrecisionData=>x.2.1) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hB : Bound (fun x : PrecisionData=>x.2.2) precisionNorm := of_le (fun x=>by unfold precisionNorm;omega)
  have hL : Bound (fun x : PrecisionData=>ladderL x.1.1.1.1 x.1.1.1.2) precisionNorm :=
    pow (mul (mul (const (10^4) _) hN) hD) 100
  have hQ : Bound (fun x : PrecisionData=>ladderQ x.1.1.1.1 x.1.1.1.2) precisionNorm := mul (const 32 _) hL
  have hM : Bound (fun x : PrecisionData=>ladderM x.1.1.1.1 x.1.1.1.2 x.1.1.2.2) precisionNorm :=
    add (mul hT (pow hQ 2)) hQ
  have hlambda : Bound (fun x : PrecisionData=>ladderLambda x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2) precisionNorm :=
    mul (mul (mul (mul (const 10 _) hN) hQ) (add hT (const 1 _)))
      (add (add hK (clog (add (mul hN hD) (const 2 _)))) (const 1 _))
  have hr : Bound (fun x : PrecisionData=>discreteLadderSteps x.1.1.1.1 x.1.1.1.2 x.1.1.2.1 x.1.1.2.2 x.1.2) precisionNorm :=
    mul (mul (mul (const 20 _) hL) hM) (add (add hlambda (clog hm)) (const 1 _))
  have he : Bound scanError precisionNorm :=
    add (add (mul (const 2 _) (add (const 1 _) hM))
      (mul (const 4 _) (add (add (mul (const 8 _) (pow hE 2)) (mul (const 4 _) hE)) (const 3 _))))
      (mul (mul (const 2 _) (pow hN 2)) hB)
  exact add (add (add (clog (mul (mul hr he) hm)) hN) hr) (clog (mul (mul (const 6 _) hE) hm))

def requestSize (x : RequestInput) : ℕ := x.1.1.2.1.2+x.2+TreeTyped.weight x
lemma weight_le_requestSize (x : RequestInput) : TreeTyped.weight x≤requestSize x := by unfold requestSize;omega
lemma bound_precision : Bound (precisionNorm ∘ sourcePrecision) requestSize := by
  have hn := NumericBounds.length (work_of_polynomial
    (polynomial_composition polynomial_requestBag polynomial_sourceVertices) X
    (fun x=>by simpa using weight_le_requestSize x))
  have he := NumericBounds.length (work_of_polynomial polynomial_requestCatalog X
    (fun x=>by simpa using weight_le_requestSize x))
  have hb := NumericBounds.length (work_of_polynomial
    (polynomial_composition polynomial_requestBag polynomial_sourceParents) X
    (fun x=>by simpa using weight_le_requestSize x))
  have hd : Bound (fun x : RequestInput=>x.1.1.2.1.2) requestSize := of_le (fun x=>by unfold requestSize;omega)
  have hs : Bound (fun x : RequestInput=>x.2) requestSize := of_le (fun x=>by unfold requestSize;omega)
  have hk : Bound (fun x : RequestInput=>x.1.1.2.1.1.2.length/2) requestSize := by
    apply of_le;intro x
    have h:=list_length_le_weight x.1.1.2.1.1.2
    have hd:=Nat.div_le_self x.1.1.2.1.1.2.length 2
    unfold requestSize
    have h1:=weight_fst x
    have h2:=weight_fst x.1
    have h3:=weight_snd x.1.1
    have h4:=weight_fst x.1.1.2
    have h5:=weight_fst x.1.1.2.1
    have h6:=weight_snd x.1.1.2.1.1
    omega
  have ht : Bound (fun x : RequestInput=>x.1.1.2.2.1.length) requestSize := by
    apply of_le;intro x
    have h:=list_length_le_weight x.1.1.2.2.1
    unfold requestSize
    have h1:=weight_fst x
    have h2:=weight_fst x.1
    have h3:=weight_snd x.1.1
    have h7:=weight_snd x.1.1.2
    have h8:=weight_fst x.1.1.2.2
    omega
  exact add (add (add (add (add (add hn hd) hk) ht) (mul (mul (const 1000 _) hk) hs)) he) hb
lemma bound_sourceRequest : Bound (OnlineSample.requestMeasure ∘ sourceRequest) requestSize := by
  have hp := NumericBounds.comp bound_plan bound_precision
  have hw := NumericBounds.weight (work_of_polynomial polynomial_sourceRequest X
    (fun x=>by simpa using weight_le_requestSize x))
  apply NumericBounds.mono (NumericBounds.add hp (NumericBounds.mul (NumericBounds.const 4 _) hw))
  intro x
  dsimp only [Function.comp_apply,sourceRequest,OnlineSample.requestMeasure,OnlineSample.scansMeasure,
    OnlineSample.pairMeasure,OnlineSample.marksMeasure]
  have h1:=weight_fst (sourceRequest x)
  have h2:=weight_fst (sourceRequest x).1
  have h3:=weight_snd (sourceRequest x)
  dsimp only [sourceRequest] at h1 h2 h3
  omega
end MatchingFPRAS.OnlineSchedule

end OAI
