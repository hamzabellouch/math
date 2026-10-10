import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNHilbert
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveStringBounds
import OAI.Combinatorics.Chromatic.Shuffle.PackOrbitBasis

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance slopeSymmetricFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

abbrev StringBlockIndex (d : I → ℕ) :=
  Σ k : ℤ,SlopeStringCoefficient a c η hc (slope c η d) d rfl k

noncomputable def homogeneousBStringEquiv (d : I → ℕ) (hd : d≠0) :
    HomogeneousBIndex a c η d ≃ StringBlockIndex a c η hc d :=
  Equiv.sigmaCongrRight (fun k=>by
    letI := slopeStringCoefficient_finite a c η hc (slope c η d) d hd rfl k
    exact (Finite.equivFinOfCardEq (slopeStringHilbert_coefficient a c η hc
      (slope c η d) d hd rfl k).symm).symm)

lemma homogeneousBStringEquiv_degree (d : I → ℕ) (hd : d≠0) (i : HomogeneousBIndex a c η d) :
    (homogeneousBStringEquiv a c η hc d hd i).1=i.1 := rfl

def HNStringIndex : List (I → ℕ) → Type u
  | [] => ULift.{u} Unit
  | d::l => StringBlockIndex a c η hc d × HNStringIndex l

def hnStringDegree : (l : List (I → ℕ)) → HNStringIndex a c η hc l → ℤ
  | [],_ => 0
  | d::l,i => i.1.1+hnStringDegree l i.2-eulerForm a d l.sum

noncomputable def hnStringEquiv : (l : List (I → ℕ)) → (∀ d∈l,d≠0) →
    HNBasisIndex a c η l ≃ HNStringIndex a c η hc l
  | [],_ => Equiv.ulift.symm
  | d::l,h => Equiv.prodCongr (homogeneousBStringEquiv a c η hc d (h d (by simp)))
      (hnStringEquiv l (fun e he=>h e (List.mem_cons_of_mem d he)))

lemma hnStringEquiv_degree (l : List (I → ℕ)) (h : ∀ d∈l,d≠0) (i : HNBasisIndex a c η l) :
    hnStringDegree a c η hc l (hnStringEquiv a c η hc l h i)=hnBasisDegree a c η l i := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rcases i with ⟨i,j⟩
    change (homogeneousBStringEquiv a c η hc d _ i).1 +
      hnStringDegree a c η hc l (hnStringEquiv a c η hc l _ j) - eulerForm a d l.sum = _
    rw [homogeneousBStringEquiv_degree, ih]
    rfl

abbrev HNStringCoefficient (d : I → ℕ) (k : ℤ) :=
  {i : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val //
    hnStringDegree a c η hc i.1.val i.2=k}

noncomputable def hnStringCoefficientEquiv (d : I → ℕ) (k : ℤ) :
    HNGradedIndex a c η d k ≃ HNStringCoefficient a c η hc d k :=
  (Equiv.sigmaCongrRight (fun l : HNIndex c η d=>
    hnStringEquiv a c η hc l.val l.property.2.1)).subtypeEquiv (by
      intro i
      exact (congrArg (·=k) (hnStringEquiv_degree a c η hc i.1.val i.1.property.2.1 i.2)).symm.to_iff)

lemma hnStringCoefficient_finite (d : I → ℕ) (k : ℤ) :
    Finite (HNStringCoefficient a c η hc d k) := by
  let := hnGradedIndex_finite a c η hc d k
  exact Finite.of_equiv _ (hnStringCoefficientEquiv a c η hc d k)

theorem finiteStringReordering_coefficient (d : I → ℕ) (k : ℤ) :
    Nat.card {i : SortedPackExponent d // (sortedPackDegree d i : ℤ)=k}=
      Nat.card (HNStringCoefficient a c η hc d k) := by
  rw [←packHilbert_coefficient,hnHilbert_coefficient a c η hc]
  exact Nat.card_congr (hnStringCoefficientEquiv a c η hc d k)
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity
variable {J : Type*} [LinearOrder J] (even : J → Prop)

def OrderedSignedWord := {l : List J // l.Pairwise (fun i j=>i≤j ∧ (i=j → even i))}
def SignedSelection := {m : Multiset J // ∀ i, ¬even i → m.count i≤1}

lemma count_le_one_of_signed_pairwise {l : List J}
    (h : l.Pairwise (fun i j=>i≤j ∧ (i=j → even i))) (i : J) (hi : ¬even i) :
    l.count i≤1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hh,ht⟩:=List.pairwise_cons.mp h
    by_cases e : i=j
    · subst j
      have hn : i∉l := fun hm=>hi ((hh i hm).2 rfl)
      simp [List.count_eq_zero.mpr hn]
    · simpa [List.count_cons,Ne.symm e] using ih ht

lemma signed_pairwise_of_count {l : List J} (h : l.Pairwise (·≤·))
    (hc : ∀ i, ¬even i → l.count i≤1) :
    l.Pairwise (fun i j=>i≤j ∧ (i=j → even i)) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    obtain ⟨hh,ht⟩:=List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro i hi
      refine ⟨hh i hi,?_⟩
      rintro rfl
      by_contra he
      have H:=hc j he
      have Hp:=List.count_pos_iff.mpr hi
      simp only [List.count_cons_self] at H
      omega
    · apply ih ht
      intro i hi
      have H:=hc i hi
      simp only [List.count_cons] at H
      split_ifs at H <;> omega

noncomputable def signedWordSelectionEquiv : OrderedSignedWord even ≃ SignedSelection even where
  toFun l := ⟨(l.val : Multiset J),by
    intro i hi
    simpa only [Multiset.coe_count] using count_le_one_of_signed_pairwise even l.property i hi⟩
  invFun m := ⟨m.val.sort (·≤·),signed_pairwise_of_count even (m.val.pairwise_sort (·≤·)) (by
    intro i hi
    have H:=m.property i hi
    have E:=congrArg (Multiset.count i) (m.val.sort_eq (·≤·))
    simpa only [Multiset.coe_count] using E.le.trans H)⟩
  left_inv l := by
    apply Subtype.ext
    exact List.Perm.eq_of_pairwise' ((l.val : Multiset J).pairwise_sort (·≤·))
      (l.property.imp (fun h=>h.1)) (Multiset.coe_eq_coe.mp ((l.val : Multiset J).sort_eq (·≤·)))
  right_inv m := Subtype.ext (m.val.sort_eq (·≤·))

lemma signedWordSelectionEquiv_val (l : OrderedSignedWord even) :
    (signedWordSelectionEquiv even l).val=(l.val : Multiset J) := rfl
end ElementaryPositivity

end

end OAI
