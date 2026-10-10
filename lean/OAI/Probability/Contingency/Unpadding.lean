import Mathlib
import OAI.Probability.Contingency.SmallPoincare

namespace OAI

/-! Unpadding. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def cellPadding (w : Cell m n) : ℤ := if IsLarge U r c w then L else 0

def largePart (Z : Tables r c) (w : Cell m n) : ℤ :=
  if IsLarge U r c w then (Z.val w.1 w.2:ℤ)+L else 0

theorem split_padding (Z : Tables r c) (w : Cell m n) :
    smallPart U r c Z w+largePart U L r c Z w=(Z.val w.1 w.2:ℤ)+cellPadding U L r c w := by
  by_cases hw : IsLarge U r c w <;> simp [smallPart,largePart,cellPadding,IsSmall,hw]

def paddedCompletion (Z : Tables r c) : Completion U L r c (initialTransversal U r c Z).val := by
  refine ⟨largePart U L r c Z,?_,?_,?_,?_⟩
  · intro w; unfold largePart; split_ifs <;> positivity
  · intro w hw; simp [largePart,show ¬IsLarge U r c w from hw]
  · intro i
    have hh : rowSum (smallPart U r c Z) i+rowSum (largePart U L r c Z) i=
        (r i:ℤ)+rowPadding U L r c i := by
      rw [rowSum,rowSum,← Finset.sum_add_distrib]
      simp only [split_padding,Finset.sum_add_distrib]
      congr 1
      exact_mod_cast Z.property.1 i
    change rowSum (largePart U L r c Z) i=(r i:ℤ)-rowSum (smallPart U r c Z) i+rowPadding U L r c i
    omega
  · intro j
    have hh : colSum (smallPart U r c Z) j+colSum (largePart U L r c Z) j=
        (c j:ℤ)+colPadding U L r c j := by
      rw [colSum,colSum,← Finset.sum_add_distrib]
      simp only [split_padding,Finset.sum_add_distrib]
      congr 1
      exact_mod_cast Z.property.2 j
    change colSum (largePart U L r c Z) j=(c j:ℤ)-colSum (smallPart U r c Z) j+colPadding U L r c j
    omega

abbrev SuccessPair := Σ X : TransverseState U r c,
  {A : Completion U L r c X.val // ∀ w,IsLarge U r c w → (L:ℤ)≤A.val w}

theorem successPair_ext (P Q : SuccessPair U L r c) (hX : P.1=Q.1)
    (hA : P.2.val.val=Q.2.val.val) : P=Q := by
  cases P with | mk X A =>
    cases Q with | mk Y B =>
      dsimp only at hX
      subst Y
      congr 1
      exact Subtype.ext (Subtype.ext hA)

def padOriginal (Z : Tables r c) : SuccessPair U L r c :=
  ⟨initialTransversal U r c Z,paddedCompletion U L r c Z,by
    intro w hw; simp [paddedCompletion,largePart,hw]⟩

def unpadEntry (P : SuccessPair U L r c) (w : Cell m n) : ℤ :=
  P.1.val.x w+P.2.val.val w-cellPadding U L r c w

theorem unpadEntry_nonneg (P : SuccessPair U L r c) (w : Cell m n) :
    0≤unpadEntry U L r c P w := by
  by_cases hw : IsLarge U r c w
  · have hx := (P.1.property.1.2.1 w hw).1
    have ha := P.2.property w hw
    simp only [unpadEntry,cellPadding,ite_eq_left hw,hx,zero_add]
    omega
  · have hx := (P.1.property.1.1 w).1
    have ha := P.2.val.property.1 w
    simp only [unpadEntry,cellPadding,ite_eq_right hw,sub_zero]
    omega

def unpadOriginal (P : SuccessPair U L r c) : Tables r c := by
  refine ⟨fun i j => (unpadEntry U L r c P (i,j)).toNat,?_,?_⟩
  · intro i
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_sum]
    have hh (w : Cell m n) : ((unpadEntry U L r c P w).toNat:ℤ)=unpadEntry U L r c P w := Int.toNat_of_nonneg (unpadEntry_nonneg U L r c P w)
    simp only [hh]
    simp only [unpadEntry,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    change rowSum P.1.val.x i+rowSum P.2.val.val i-rowPadding U L r c i= r i
    rw [P.2.val.property.2.2.1 i]
    ring
  · intro j
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_sum]
    have hh (w : Cell m n) : ((unpadEntry U L r c P w).toNat:ℤ)=unpadEntry U L r c P w := Int.toNat_of_nonneg (unpadEntry_nonneg U L r c P w)
    simp only [hh]
    simp only [unpadEntry,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    change colSum P.1.val.x j+colSum P.2.val.val j-colPadding U L r c j=c j
    rw [P.2.val.property.2.2.2 j]
    have ht : P.1.val.q=P.1.val.x := P.1.property.2
    rw [ht]
    ring

@[simp] theorem unpad_pad (Z : Tables r c) : unpadOriginal U L r c (padOriginal U L r c Z)=Z := by
  apply Subtype.ext; funext i j
  change (smallPart U r c Z (i,j)+largePart U L r c Z (i,j)-cellPadding U L r c (i,j)).toNat=Z.val i j
  rw [split_padding,add_sub_cancel_right,Int.toNat_natCast]

@[simp] theorem pad_unpad (P : SuccessPair U L r c) : padOriginal U L r c (unpadOriginal U L r c P)=P := by
  have hv (w : Cell m n) : ((unpadOriginal U L r c P).val w.1 w.2:ℤ)=unpadEntry U L r c P w :=
    Int.toNat_of_nonneg (unpadEntry_nonneg U L r c P w)
  have hs : smallPart U r c (unpadOriginal U L r c P)=P.1.val.x := by
    funext w
    by_cases hw : IsLarge U r c w
    · simp [smallPart,IsSmall,hw,(P.1.property.1.2.1 w hw).1]
    · simp only [smallPart,IsSmall,ite_eq_left hw,hv,unpadEntry,cellPadding,ite_eq_right hw,sub_zero,
        P.2.val.property.2.1 w hw,add_zero]
  have ha : largePart U L r c (unpadOriginal U L r c P)=P.2.val.val := by
    funext w
    by_cases hw : IsLarge U r c w
    · simp [largePart,hw,hv,unpadEntry,cellPadding,(P.1.property.1.2.1 w hw).1]
    · simp [largePart,hw,P.2.val.property.2.1 w hw]
  have hx : initialTransversal U r c (unpadOriginal U L r c P)=P.1 := by
    apply Subtype.ext
    apply State.ext
    · exact hs
    · exact hs.trans P.1.property.2.symm
  exact successPair_ext U L r c _ _ hx ha

 

def successEquiv : Tables r c ≃ SuccessPair U L r c where
  toFun := padOriginal U L r c
  invFun := unpadOriginal U L r c
  left_inv := unpad_pad U L r c
  right_inv := pad_unpad U L r c

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (p : Fin m → Fin n → ℕ)

def shiftedRow (i : Fin m) : ℕ := r i+∑ j,p i j
def shiftedCol (j : Fin n) : ℕ := c j+∑ i,p i j
abbrev ShiftPassing := {A : Tables (shiftedRow r p) (shiftedCol c p) // ∀ i j,p i j≤A.val i j}

def shiftTable (Z : Tables r c) : ShiftPassing r c p := by
  refine ⟨⟨fun i j => Z.val i j+p i j,?_,?_⟩,?_⟩
  · intro i; simp only [Finset.sum_add_distrib,Z.property.1,shiftedRow]
  · intro j; simp only [Finset.sum_add_distrib,Z.property.2,shiftedCol]
  · intro i j; dsimp; omega

def unshiftTable (A : ShiftPassing r c p) : Tables r c := by
  refine ⟨fun i j => A.val.val i j-p i j,?_,?_⟩
  · intro i
    apply Nat.add_right_cancel (m:=∑ j,p i j)
    calc
      _ = ∑ j,(A.val.val i j-p i j+p i j) := by rw [Finset.sum_add_distrib]
      _ = ∑ j,A.val.val i j := Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (A.property i j))
      _ = r i+∑ j,p i j := A.val.property.1 i
  · intro j
    apply Nat.add_right_cancel (m:=∑ i,p i j)
    calc
      _ = ∑ i,(A.val.val i j-p i j+p i j) := by rw [Finset.sum_add_distrib]
      _ = ∑ i,A.val.val i j := Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (A.property i j))
      _ = c j+∑ i,p i j := A.val.property.2 j

def shiftEquiv : Tables r c ≃ ShiftPassing r c p where
  toFun := shiftTable r c p
  invFun := unshiftTable r c p
  left_inv Z := by apply Subtype.ext; funext i j; exact Nat.add_sub_cancel_right _ _
  right_inv A := by apply Subtype.ext; apply Subtype.ext; funext i j; exact Nat.sub_add_cancel (A.property i j)

theorem shift_card : Nat.card (ShiftPassing r c p)=Nat.card (Tables r c) :=
  Nat.card_congr (shiftEquiv r c p).symm

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def naturalPadding (i : Fin m) (j : Fin n) : ℕ := if IsLarge U r c (i,j) then L else 0
abbrev Enlarged := Tables (shiftedRow r (naturalPadding U L r c)) (shiftedCol c (naturalPadding U L r c))
abbrev EnlargedBad := {A : Enlarged U L r c // ¬∀ i j,naturalPadding U L r c i j≤A.val i j}
abbrev LargeCell := {w : Cell m n // IsLarge U r c w}

theorem enlarged_partition : Nat.card (Tables r c)+Nat.card (EnlargedBad U L r c)=Nat.card (Enlarged U L r c) := by
  classical
  have hh := Nat.card_congr (Equiv.sumCompl (fun A : Enlarged U L r c => ∀ i j,naturalPadding U L r c i j≤A.val i j))
  rw [Nat.card_sum,shift_card] at hh
  exact hh

theorem enlarged_bad_union : Nat.card (EnlargedBad U L r c) ≤
    ∑ w : LargeCell U r c, Nat.card (SmallEntryBad
      (shiftedRow r (naturalPadding U L r c)) (shiftedCol c (naturalPadding U L r c)) w.val.1 w.val.2 L) := by
  classical
  have hb (A : EnlargedBad U L r c) : ∃ w : LargeCell U r c,A.val.val w.val.1 w.val.2<L := by
    have h := A.property
    push Not at h
    obtain ⟨i,j,h⟩ := h
    have hw : IsLarge U r c (i,j) := by by_contra hw; simp [naturalPadding,hw] at h
    exact ⟨⟨(i,j),hw⟩,by simpa [naturalPadding,hw] using h⟩
  let F : EnlargedBad U L r c → Σ w : LargeCell U r c, SmallEntryBad
      (shiftedRow r (naturalPadding U L r c)) (shiftedCol c (naturalPadding U L r c)) w.val.1 w.val.2 L :=
    fun A => ⟨(hb A).choose,⟨A.val,(hb A).choose_spec⟩⟩
  have hi : Function.Injective F := by
    intro A B h
    apply Subtype.ext
    exact congrArg (fun z : Σ w : LargeCell U r c, SmallEntryBad
      (shiftedRow r (naturalPadding U L r c)) (shiftedCol c (naturalPadding U L r c)) w.val.1 w.val.2 L => z.2.val) h
  have hh := Nat.card_le_card_of_injective F hi
  rwa [Nat.card_sigma] at hh

theorem enlarged_bad_count (d : ℕ) (hd : 1≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d)
    (hU : 4*d≤U) (hL : 2*L≤U) :
    Nat.card (EnlargedBad U L r c)*U ≤ 4*L*d^4*Nat.card (Enlarged U L r c) := by
  classical
  have hdim : Fintype.card (LargeCell U r c)≤d := by
    have hh := Fintype.card_subtype_le (fun w : Cell m n => IsLarge U r c w)
    simpa [Cell] using hh.trans (by simpa [Cell] using hmn)
  calc
    _ ≤ (∑ w : LargeCell U r c,Nat.card (SmallEntryBad
      (shiftedRow r (naturalPadding U L r c)) (shiftedCol c (naturalPadding U L r c)) w.val.1 w.val.2 L))*U :=
        Nat.mul_le_mul_right U (enlarged_bad_union U L r c)
    _ ≤ ∑ _w : LargeCell U r c,4*L*d^3*Nat.card (Enlarged U L r c) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro w _
      exact small_entry_count d U L _ _ w.val.1 w.val.2 hd hm hn hU
        (w.property.1.trans (Nat.le_add_right _ _)) (w.property.2.trans (Nat.le_add_right _ _)) hL
    _ ≤ d*(4*L*d^3*Nat.card (Enlarged U L r c)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ hdim
    _ = _ := by ring

abbrev TransverseJoint := Σ X : TransverseState U r c,Completion U L r c X.val

def enlargedOfTransverse (P : TransverseJoint U L r c) : Enlarged U L r c := by
  refine ⟨fun i j => (P.1.val.x (i,j)+P.2.val (i,j)).toNat,?_,?_⟩
  · intro i
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_sum]
    have hh (w : Cell m n) : ((P.1.val.x w+P.2.val w).toNat:ℤ)=P.1.val.x w+P.2.val w :=
      Int.toNat_of_nonneg (add_nonneg (P.1.property.1.1 w).1 (P.2.property.1 w))
    simp only [hh,Finset.sum_add_distrib]
    change rowSum P.1.val.x i+rowSum P.2.val i=(shiftedRow r (naturalPadding U L r c) i:ℤ)
    rw [P.2.property.2.2.1 i]
    simp only [shiftedRow,Nat.cast_add,Nat.cast_sum,naturalPadding,Nat.cast_ite,Nat.cast_zero,rowPadding]
    ring
  · intro j
    apply Int.ofNat_inj.mp
    simp only [Nat.cast_sum]
    have hh (w : Cell m n) : ((P.1.val.x w+P.2.val w).toNat:ℤ)=P.1.val.x w+P.2.val w :=
      Int.toNat_of_nonneg (add_nonneg (P.1.property.1.1 w).1 (P.2.property.1 w))
    simp only [hh,Finset.sum_add_distrib]
    change colSum P.1.val.x j+colSum P.2.val j=(shiftedCol c (naturalPadding U L r c) j:ℤ)
    rw [P.2.property.2.2.2 j,P.1.property.2]
    simp only [shiftedCol,Nat.cast_add,Nat.cast_sum,naturalPadding,Nat.cast_ite,Nat.cast_zero,colPadding]
    ring

theorem enlargedOfTransverse_injective : Function.Injective (enlargedOfTransverse U L r c) := by
  intro P Q h
  have he (w : Cell m n) : P.1.val.x w+P.2.val w=Q.1.val.x w+Q.2.val w := by
    have hh := congrArg (fun Z : Enlarged U L r c => Z.val w.1 w.2) h
    change (P.1.val.x w+P.2.val w).toNat=(Q.1.val.x w+Q.2.val w).toNat at hh
    have hp := add_nonneg (P.1.property.1.1 w).1 (P.2.property.1 w)
    have hq := add_nonneg (Q.1.property.1.1 w).1 (Q.2.property.1 w)
    omega
  have hx : P.1.val.x=Q.1.val.x := by
    funext w
    by_cases hw : IsLarge U r c w
    · rw [(P.1.property.1.2.1 w hw).1,(Q.1.property.1.2.1 w hw).1]
    · have hh := he w
      rw [P.2.property.2.1 w hw,Q.2.property.2.1 w hw] at hh
      simpa using hh
  have hX : P.1=Q.1 := by
    apply Subtype.ext
    apply State.ext hx
    rw [P.1.property.2,Q.1.property.2,hx]
  have hA : P.2.val=Q.2.val := by funext w; have hh := he w; have hw := congrFun hx w; omega
  cases P with | mk X A =>
    cases Q with | mk Y B =>
      dsimp only at hX
      subst Y
      congr 1
      exact Subtype.ext hA

theorem transverseMass_enlarged : transverseMass U L r c≤Nat.card (Enlarged U L r c) := by
  have hh := Nat.card_le_card_of_injective _ (enlargedOfTransverse_injective U L r c)
  rw [Nat.card_sigma] at hh
  convert hh using 1
  unfold transverseMass
  apply Finset.sum_congr rfl
  intro X _
  rw [weight,ite_eq_left X.property.1]

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
variable {m n : ℕ} (d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem enlarged_half (hd : 14≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d) :
    Nat.card (Enlarged (d^20) (d^12) r c)≤2*Nat.card (Tables r c) := by
  have hd1 : 1≤d := by omega
  have h19 : 4≤d^19 := (by norm_num : 4≤14^19).trans (Nat.pow_le_pow_left hd _)
  have h8 : 2≤d^8 := (by norm_num : 2≤14^8).trans (Nat.pow_le_pow_left hd _)
  have h4 : 8≤d^4 := (by norm_num : 8≤14^4).trans (Nat.pow_le_pow_left hd _)
  have hU : 4*d≤d^20 := by nlinarith only [Nat.mul_le_mul_right d h19,show d^20=d^19*d by ring]
  have hL : 2*d^12≤d^20 := by nlinarith only [Nat.mul_le_mul_left (d^12) h8,show d^20=d^12*d^8 by ring]
  have hhalf : 2*(4*d^12*d^4)≤d^20 := by
    nlinarith only [Nat.mul_le_mul_left (d^16) h4,show d^20=d^16*d^4 by ring,show d^12*d^4=d^16 by ring]
  have hh := enlarged_bad_count (d^20) (d^12) r c d hd1 hm hn hmn hU hL
  have hwhole := enlarged_partition (d^20) (d^12) r c
  have hc' := Nat.mul_le_mul_right (Nat.card (Enlarged (d^20) (d^12) r c)) hhalf
  have hb : 2*Nat.card (EnlargedBad (d^20) (d^12) r c)≤Nat.card (Enlarged (d^20) (d^12) r c) := by
    by_contra h
    have hpos : 0<d^20 := pow_pos (by omega) _
    have hgt := Nat.mul_lt_mul_of_pos_right (show Nat.card (Enlarged (d^20) (d^12) r c)<2*Nat.card (EnlargedBad (d^20) (d^12) r c) by omega) hpos
    nlinarith only [hh,hc',hgt]
  omega

 
theorem stationary_success_count (hd : 14≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d)
    (hrc : (∑ i,r i)=∑ j,c j) :
    graphMass (d^20) (d^12) r c≤2*(1+d^2)*Nat.card (Tables r c) := by
  have hw := (graphMass_bounds (d^20) (d^12) d r c hrc hmn).2.2
  have he := (transverseMass_enlarged (d^20) (d^12) r c).trans (enlarged_half d r c hd hm hn hmn)
  nlinarith only [hw,Nat.mul_le_mul_left (1+d^2) he]

theorem stationary_success_probability (hd : 14≤d) (hm : m≤d) (hn : n≤d) (hmn : m*n≤d)
    (hrc : (∑ i,r i)=∑ j,c j) :
    1/(2*(1+(d:ℝ)^2))≤(Nat.card (Tables r c):ℝ)/graphMass (d^20) (d^12) r c := by
  have hpos := graphMass_bounds (d^20) (d^12) d r c hrc hmn
  have hp : (0:ℝ)<graphMass (d^20) (d^12) r c := by exact_mod_cast lt_of_lt_of_le hpos.1 hpos.2.1
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  have hh : (graphMass (d^20) (d^12) r c:ℝ)≤2*(1+(d:ℝ)^2)*Nat.card (Tables r c) := by
    exact_mod_cast stationary_success_count d r c hd hm hn hmn hrc
  nlinarith only [hh]

variable (U L : ℕ)
local instance unpaddingDecodeTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

def successfulJoint (Z : Tables r c) : Joint U L r c := ⟨Sum.inl (initialTransversal U r c Z),paddedCompletion U L r c Z⟩

def decodeJoint (P : Joint U L r c) : Option (Tables r c) := by
  classical
  match P with
  | ⟨Sum.inl X,A⟩ => exact if h : ∀ w,IsLarge U r c w → (L:ℤ)≤A.val w then some (unpadOriginal U L r c ⟨X,A,h⟩) else none
  | ⟨Sum.inr _,_⟩ => exact none

theorem decodeJoint_eq_some (P : Joint U L r c) (Z : Tables r c) :
    decodeJoint r c U L P=some Z ↔ P=successfulJoint r c U L Z := by
  classical
  cases P with | mk X A =>
    cases X with
    | inr X =>
      simp only [decodeJoint,reduceCtorEq,false_iff]
      intro h
      have hh := congrArg (fun s : Joint U L r c => s.1) h
      change Sum.inr X=Sum.inl (initialTransversal U r c Z) at hh
      cases hh
    | inl X =>
      change (if h : ∀ w,IsLarge U r c w → (L:ℤ)≤A.val w then some (unpadOriginal U L r c ⟨X,A,h⟩) else none)=some Z ↔ _
      split_ifs with h
      · rw [Option.some.injEq]
        constructor
        · intro he
          have hh := congrArg (padOriginal U L r c) he
          rw [pad_unpad] at hh
          have hx := congrArg (fun s : SuccessPair U L r c => s.1) hh
          have ha := congrArg (fun s : SuccessPair U L r c => s.2.val.val) hh
          change X=initialTransversal U r c Z at hx
          subst X
          congr 1
          exact Subtype.ext ha
        · intro he
          have hx := congrArg (fun s : Joint U L r c => s.1) he
          have hX : X=initialTransversal U r c Z := Sum.inl.inj hx
          have hA := congrArg (fun s : Joint U L r c => s.2.val) he
          have hh := successPair_ext U L r c ⟨X,A,h⟩ (padOriginal U L r c Z) hX hA
          rw [hh,unpad_pad]
      · simp only [false_iff]
        intro he
        have ha := congrArg (fun s : Joint U L r c => s.2.val) he
        apply h
        intro w hw
        have hew := congrFun ha w
        change A.val w=largePart U L r c Z w at hew
        rw [hew]
        simp [largePart,hw]

variable [Nonempty (Tables r c)]
local instance unpaddingJointNonempty : Nonempty (Joint U L r c) := Nonempty.map (successfulJoint r c U L) inferInstance

def stationaryTrial : Law (Option (Tables r c)) := (Law.uniform (Joint U L r c)).map (decodeJoint r c U L)

theorem stationaryTrial_some (Z : Tables r c) :
    (stationaryTrial r c U L).mass (some Z)=1/(graphMass U L r c:ℝ) := by
  classical
  simp only [stationaryTrial,Law.map,Law.bind,Law.pure,mul_ite,mul_one,mul_zero,decodeJoint_eq_some]
  simp only [Law.uniform,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Nat.card_eq_fintype_card,joint_card]

theorem stationaryTrial_none : (stationaryTrial r c U L).mass none=
    1-(Nat.card (Tables r c):ℝ)/graphMass U L r c := by
  have ht := (stationaryTrial r c U L).total
  rw [Fintype.sum_option] at ht
  simp only [stationaryTrial_some,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  rw [← Nat.card_eq_fintype_card] at ht
  simp only [one_div,← div_eq_mul_inv] at ht
  linarith

theorem stationaryTrial_uniform (Z : Tables r c) :
    (stationaryTrial r c U L).mass (some Z)=
      (1-(stationaryTrial r c U L).mass none)*(Law.uniform (Tables r c)).mass Z := by
  rw [stationaryTrial_some,stationaryTrial_none]
  simp only [Law.uniform,sub_sub_cancel,← Nat.card_eq_fintype_card]
  have hp : (Nat.card (Tables r c):ℝ)≠0 := by exact_mod_cast (Nat.card_pos (α:=Tables r c)).ne'
  field_simp

end
end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n a c' : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U ≤ r i}) (ec : Fin c' ≃ {j // U ≤ c j}) (i₀ : Fin a) (j₀ : Fin c')
    (hrc : (∑ i,r i)=∑ j,c j) (hd : 1 ≤ d) (hmn : m*n ≤ d)
    [Nonempty (GraphState U r c)]

local notation "Comp" => fun X : GraphState U r c => Completion U L r c (graphUnderlying U r c X)
local instance unpaddingInvariantCompFintype (X : GraphState U r c) : Fintype (Comp X) := Fintype.ofFinite _
local instance unpaddingInvariantTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

theorem invariant_joint :
    letI := tables_nonempty r c hrc
    letI : Nonempty (Joint U L r c) := Nonempty.map (successfulJoint r c U L) inferInstance
    ((smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.invariant).sigma
      (idealCompletion U L r c hrc)=Law.uniform (Joint U L r c) := by
  classical
  let := tables_nonempty r c hrc
  let : Nonempty (Joint U L r c) := Nonempty.map (successfulJoint r c U L) inferInstance
  apply Law.ext; funext ⟨X,A⟩
  simp only [Law.sigma,Chain.invariant,AcceptedData.chain,smallData,idealCompletion,Law.uniform]
  have htotal : (∑ X : GraphState U r c,(weight U L r c (graphUnderlying U r c X):ℝ))=(graphMass U L r c:ℝ) := by
    simp [graphMass,Nat.cast_sum]
  change (weight U L r c (graphUnderlying U r c X):ℝ)/
      (∑ X : GraphState U r c,(weight U L r c (graphUnderlying U r c X):ℝ)) *
      (1/(Fintype.card (Comp X):ℝ)) = 1/(Fintype.card (Joint U L r c):ℝ)
  rw [htotal,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,joint_card]
  have he : weight U L r c (graphUnderlying U r c X)=Nat.card (Comp X) := by
    rw [weight,ite_eq_left (graph_feasible U r c X)]
  rw [← he]
  have hp : (weight U L r c (graphUnderlying U r c X):ℝ)≠0 := by
    exact_mod_cast (graph_weight_pos U L r c X hrc).ne'
  field_simp

def jointTrial (p : Law (GraphState U r c)) (μ : ∀ X,Law (Comp X)) : Law (Option (Tables r c)) :=
  (p.sigma μ).map (decodeJoint r c U L)

theorem jointTrial_tv (p : Law (GraphState U r c)) (μ : ∀ X,Law (Comp X)) (δ : ℝ)
    (hμ : ∀ X,(μ X).tv (idealCompletion U L r c hrc X) ≤ δ) :
    letI := tables_nonempty r c hrc
    (jointTrial U L r c p μ).tv (stationaryTrial r c U L) ≤
      p.tv (smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.invariant+δ := by
  classical
  let := tables_nonempty r c hrc
  unfold jointTrial stationaryTrial
  rw [← invariant_joint U L d r c er ec i₀ j₀ hrc hd hmn]
  exact (Law.tv_map _ _ _).trans (Law.tv_sigma _ _ _ _ δ hμ)

end
end Contingency.PaddedGraph

 

 

namespace Contingency.Schedule

theorem exp_neg_binary (x : ℝ) (N : ℕ) (hx : (N:ℝ)≤x) :
    Real.exp (-x)≤(2:ℝ)^(-(N:ℤ)) := by
  have hl : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have he : (2:ℝ)^(-(N:ℤ)) = Real.exp (-((N:ℝ)*Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2), zpow_neg, zpow_natCast]
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg N : (0:ℝ)≤N)]

variable (d b k : ℕ) (hd : 14≤d) (hb : d≤b) (hk : 1≤k)

include hd hk in
theorem failure_schedule : Real.exp (-((Jo d k:ℝ)/(2*(1+(d:ℝ)^2))))≤(2:ℝ)^(-((k+2:ℕ):ℤ)) := by
  apply exp_neg_binary
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(1+(d:ℝ)^2))).mpr
  have hd2 : (4:ℝ)≤(d:ℝ)^2 := by exact_mod_cast (show 4≤d^2 from (by norm_num : 4≤14^2).trans (Nat.pow_le_pow_left hd _))
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  simp only [Jo,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have he : (d:ℝ)^4=((d:ℝ)^2)^2 := by ring
  nlinarith [mul_nonneg (show 0≤(d:ℝ)^2-4 by linarith) (show 0≤(d:ℝ)^2-1 by linarith)]

theorem jo_binary : Jo d k≤2^(4*d+k) := by
  calc
    _ ≤ (2^d)^4*2^k := Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=d)).le 4) (Nat.lt_two_pow_self (n:=k))
    _ = _ := by rw [← pow_mul,← pow_add]; congr 1; omega

theorem transition_binary : T d b k≤2^(200*d+2*(k+b)) := by
  calc
    _ ≤ (2^d)^200*(2^(k+b))^2 := Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=d)).le 200) (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n:=k+b)).le 2)
    _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; omega

include hd hb hk in
theorem offset_schedule : (Jo d k:ℝ)*(T d b k+1)*(2:ℝ)^(-(h d b k:ℤ))≤(2:ℝ)^(-((k+2:ℕ):ℤ)) := by
  have hT : 1≤T d b k := by unfold T; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hJ := jo_binary d k
  have ht := transition_binary d b k
  have he : Jo d k*(T d b k+1)*2^(k+2)≤2^(204*d+2*k+2*(k+b)+3) := by
    calc
      _ ≤ (2^(4*d+k))*(2*2^(200*d+2*(k+b)))*2^(k+2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hJ (by omega))
      _ = _ := by rw [show 2*2^(200*d+2*(k+b))=2^(200*d+2*(k+b)+1) by rw [pow_succ]; omega,← pow_add,← pow_add]; congr 1; omega
  have hd4 : 209≤d^4 := (by norm_num : 209≤14^4).trans (Nat.pow_le_pow_left hd _)
  have hexp : 204*d+2*k+2*(k+b)+3≤h d b k := by
    have ht1 : 1≤k+b := by omega
    have htt : k+b≤(k+b)^2 := Nat.le_self_pow (by omega) _
    have hh := Nat.mul_le_mul hd4 htt
    unfold h
    nlinarith only [hh,hb,hk,hd]
  have H := he.trans (Nat.pow_le_pow_right (by omega) hexp)
  rw [zpow_neg,zpow_natCast,zpow_neg,zpow_natCast,← div_eq_mul_inv,inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat,one_mul] using (show ((Jo d k*(T d b k+1)*2^(k+2):ℕ):ℝ)≤(2:ℝ)^(h d b k) by exact_mod_cast H)

include hd hb hk in
theorem mixing_schedule (C : ℕ) (hC : C+1≤2^b) :
    (Jo d k:ℝ)*(C+1:ℝ)^(2*d)*Real.exp (-((T d b k:ℝ)/(d:ℝ)^160))≤(2:ℝ)^(-((k+2:ℕ):ℤ)) := by
  let E := 4*d+k+2*d*b
  have hcoeff : Jo d k*(C+1)^(2*d)≤2^E := by
    calc
      _ ≤ 2^(4*d+k)*(2^b)^(2*d) := Nat.mul_le_mul (jo_binary d k) (Nat.pow_le_pow_left hC _)
      _ = _ := by rw [← pow_mul,← pow_add]; congr 1; dsimp [E]; ring
  have hdp : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hdiv : (T d b k:ℝ)/(d:ℝ)^160=(d:ℝ)^40*(k+b:ℝ)^2 := by
    simp only [T,Nat.cast_mul,Nat.cast_pow,Nat.cast_add]
    have he : (d:ℝ)^200=(d:ℝ)^160*(d:ℝ)^40 := by rw [← pow_add]
    rw [he]
    field_simp
  have hE : E+k+2≤3*(k+b)^2 := by
    dsimp [E]
    have hdb := Nat.mul_le_mul (show d≤k+b by omega) (show b≤k+b by omega)
    nlinarith only [hdb,hb,hk,hd]
  have hd40 : 3≤d^40 := (by norm_num : 3≤14^40).trans (Nat.pow_le_pow_left hd _)
  have hg : (E+k+2:ℕ)≤d^40*(k+b)^2 := hE.trans (Nat.mul_le_mul_right _ hd40)
  have hx : ((E+k+2:ℕ):ℝ)≤(T d b k:ℝ)/(d:ℝ)^160 := by rw [hdiv]; exact_mod_cast hg
  have he := exp_neg_binary _ (E+k+2) hx
  calc
    _ ≤ (2:ℝ)^E*(2:ℝ)^(-((E+k+2:ℕ):ℤ)) := by
      exact mul_le_mul (by exact_mod_cast hcoeff) he (Real.exp_pos _).le (by positivity)
    _ = (2:ℝ)^(-((k+2:ℕ):ℤ)) := by
      rw [zpow_neg,zpow_natCast,zpow_neg,zpow_natCast,show E+k+2=E+(k+2) by omega,pow_add]
      field_simp
      simp [E,pow_add]

include hd hb hk in
theorem outer_error_schedule (C : ℕ) (hC : C+1≤2^b) :
    Real.exp (-((Jo d k:ℝ)/(2*(1+(d:ℝ)^2))))+
      (Jo d k:ℝ)*(C+1:ℝ)^(2*d)*Real.exp (-((T d b k:ℝ)/(d:ℝ)^160))+
      (Jo d k:ℝ)*(T d b k+1)*(2:ℝ)^(-(h d b k:ℤ))≤(2:ℝ)^(-(k:ℤ)) := by
  have hf := failure_schedule d k hd hk
  have hm := mixing_schedule d b k hd hb hk C hC
  have ho := offset_schedule d b k hd hb hk
  have he : (2:ℝ)^(-((k+2:ℕ):ℤ))=(2:ℝ)^(-(k:ℤ))/4 := by
    rw [zpow_neg,zpow_natCast,zpow_neg,zpow_natCast,pow_add]
    norm_num
    ring
  rw [he] at hf hm ho
  have hp : (0:ℝ)≤(2:ℝ)^(-(k:ℤ)) := by positivity
  linarith

end Contingency.Schedule

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
noncomputable section
open FiniteChain
variable {m n a c' : ℕ} (U L d : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (er : Fin a ≃ {i // U ≤ r i}) (ec : Fin c' ≃ {j // U ≤ c j}) (i₀ : Fin a) (j₀ : Fin c')
    (hd : 1 ≤ d) (hmn : m*n ≤ d)
local notation "Comp" => fun X : GraphState U r c => Completion U L r c (graphUnderlying U r c X)
local instance unpaddingTrialCompFintype (X : GraphState U r c) : Fintype (Comp X) := Fintype.ofFinite _
local instance unpaddingTrialTablesFintype : Fintype (Tables r c) := Fintype.ofFinite _

def implementedTrial (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X₀ : GraphState U r c) (t : ℕ) : DyadicLaw (Option (Tables r c)) := by
  classical
  exact ((implementedWalk U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).sigma μ S hS).map (decodeJoint r c U L)

theorem implementedTrial_bits (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X₀ : GraphState U r c) (t : ℕ) :
    (implementedTrial U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).bits=t*(Nat.clog 2 (32*d^2)+S)+S := by
  classical
  simp only [implementedTrial,DyadicLaw.map_bits,DyadicLaw.sigma_bits,implementedWalk,DyadicLaw.walk_bits]

theorem toLaw_implementedTrial (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (X₀ : GraphState U r c) (t : ℕ) :
    (implementedTrial U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).toLaw=
      jointTrial U L r c (implementedWalk U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).toLaw (fun X => (μ X).toLaw) := by
  classical
  simp only [implementedTrial,DyadicLaw.toLaw_map,DyadicLaw.toLaw_sigma,jointTrial]

variable (hrc : (∑ i,r i)=∑ j,c j) [Nonempty (GraphState U r c)]

theorem implementedTrial_tv (μ : ∀ X,DyadicLaw (Comp X)) (S : ℕ) (hS : ∀ X,(μ X).bits=S)
    (δ : ℝ) (hμ : ∀ X,(μ X).toLaw.tv (idealCompletion U L r c hrc X)≤δ)
    (X₀ : GraphState U r c) (t : ℕ) :
    letI := tables_nonempty r c hrc
    (implementedTrial U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).toLaw.tv (stationaryTrial r c U L)≤
      ((smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.walk X₀ t).tv
        (smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.invariant+((t:ℝ)+1)*δ := by
  classical
  let := tables_nonempty r c hrc
  rw [toLaw_implementedTrial]
  have hj := jointTrial_tv U L d r c er ec i₀ j₀ hrc hd hmn (implementedWalk U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).toLaw (fun X => (μ X).toLaw) δ hμ
  have hw := implementedWalk_tv U L d r c er ec i₀ j₀ hrc hd hmn μ S hS δ hμ X₀ t
  have ht := Law.tv_triangle (implementedWalk U L d r c er ec i₀ j₀ hd hmn μ S hS X₀ t).toLaw
    ((smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.walk X₀ t)
    (smallData U L d r c er ec i₀ j₀ hrc hd hmn).chain.invariant
  linarith

end
end Contingency.PaddedGraph

end

end OAI
