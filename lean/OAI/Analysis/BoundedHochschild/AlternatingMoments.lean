import Mathlib
import OAI.Analysis.BoundedHochschild.FreeCoefficients
import OAI.Analysis.BoundedHochschild.UltrapowerMoments

namespace OAI

/-! Integer powers, alternating words and graded free moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder
namespace HochschildPatching
variable {I : Type*} {M : Type*} [CStarAlgebra M]
abbrev IntAtom (I : Type*) := ℤ × Option I

def integerEval (F : I → M) (u : unitary M) (a : Option I) (l : List (IntAtom I)) : M :=
  wordCoeff F a * (l.map (fun b => ((u^b.1 : unitary M):M)*wordCoeff F b.2)).prod

def admissibleIntTail (l : List (IntAtom I)) : Prop :=
  l ≠ [] ∧ ∀ b ∈ l.dropLast, b.2 ≠ none

def exponentCode (k : ℤ) : Bool × ℕ := (decide (k<0), k.natAbs-1)
lemma signed_exponentCode (k : ℤ) (hk : k ≠ 0) : signedExponent (exponentCode k)=k := by
  have hn : (k.natAbs-1:ℕ)+1=k.natAbs := Nat.sub_add_cancel (Int.natAbs_pos.mpr hk)
  have hn' : ((k.natAbs-1:ℕ):ℤ)+1=(k.natAbs:ℤ) := by exact_mod_cast hn
  simp only [exponentCode,signedExponent,hn',Int.natCast_natAbs]
  by_cases hh : k<0
  · simp [hh,abs_of_neg hh]
  · simp [hh,abs_of_nonneg (le_of_not_gt hh)]

def toIntAtom {K : ℕ} (b : WordAtom I K) : IntAtom I := (signedExponent (b.1.1,b.1.2.val),b.2)
lemma integerEval_toIntAtom {K : ℕ} (F : I → M) (u : unitary M) (a : Option I) (l : List (WordAtom I K)) :
    integerEval F u a (l.map toIntAtom)=mixedEval F (asPartialUnitary u) a l := by
  rw [mixedEval_unitary_product]
  simp only [integerEval,List.map_map]
  rfl

lemma integer_moments_of_bounded (τ : M → ℂ) (F : I → M) (u : unitary M)
    (hm : ∀ K : ℕ, ∀ a : Option I, ∀ l : List (WordAtom I K),
      admissibleTail l → τ (mixedEval F (asPartialUnitary u) a l)=0)
    (a : Option I) (l : List (IntAtom I)) (hl : admissibleIntTail l)
    (hk : ∀ b ∈ l, b.1 ≠ 0) : τ (integerEval F u a l)=0 := by
  classical
  let s : Finset ℕ := (l.map (fun b => (exponentCode b.1).2)).toFinset
  obtain ⟨K,hK⟩ := s.exists_nat_subset_range
  let g : IntAtom I → WordAtom I (K+1) := fun b =>
    (( (exponentCode b.1).1, if h : (exponentCode b.1).2 < K+1 then ⟨(exponentCode b.1).2,h⟩ else ⟨0,Nat.zero_lt_succ K⟩),b.2)
  have hg (b : IntAtom I) (hb : b ∈ l) : toIntAtom (g b)=b := by
    have hh : (exponentCode b.1).2 < K := Finset.mem_range.mp (hK (List.mem_toFinset.mpr (List.mem_map.mpr ⟨b,hb,rfl⟩)))
    dsimp only [g,toIntAtom]
    rw [dite_eq_left (Nat.lt_succ_of_lt hh)]
    change (signedExponent (exponentCode b.1),b.2)=b
    rw [signed_exponentCode _ (hk b hb)]
  have hmap : (l.map g).map toIntAtom=l := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    exact List.map_congr_left hg
  have had : admissibleTail (l.map g) := by
    constructor
    · intro h; exact hl.1 (List.map_eq_nil_iff.mp h)
    · intro b hb
      rw [← List.map_dropLast] at hb
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      exact hl.2 c hc
  have ht := hm (K+1) a (l.map g) had
  rw [← integerEval_toIntAtom,hmap] at ht
  exact ht
end HochschildPatching

 

 

namespace HochschildPatching
variable {I H M : Type*} [CStarAlgebra M]
def alternatingTag : I ⊕ H → Bool := Sum.elim (fun _ => false) (fun _ => true)
lemma intTail_cons {t : List (IntAtom I)} (ht : admissibleIntTail t) (k : ℤ) (i : I) :
    admissibleIntTail ((k,some i)::t) := by
  refine ⟨List.cons_ne_nil _ _,?_⟩
  rw [List.dropLast_cons_of_ne_nil ht.1]
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp
  · exact ht.2 b hb

lemma alternating_right_repr (F : I → M) (R : H → M) (u : unitary M)
    (hR : ∀ h, R h=0 ∨ ∃ k : ℤ, k ≠ 0 ∧ R h=((u^k : unitary M):M))
    (h : H) (l : List (I ⊕ H))
    (hc : (Sum.inr h::l).IsChain (fun x y => alternatingTag x ≠ alternatingTag y))
    (hnz : ∀ h', Sum.inr h' ∈ Sum.inr h::l → R h' ≠ 0) :
    ∃ t : List (IntAtom I), admissibleIntTail t ∧ (∀ b ∈ t, b.1 ≠ 0) ∧
      ((Sum.inr h::l).map (Sum.elim F R)).prod=integerEval F u none t := by
  suffices hx : ∀ n : ℕ, ∀ l : List (I ⊕ H), l.length=n → ∀ h : H,
      (Sum.inr h::l).IsChain (fun x y => alternatingTag x ≠ alternatingTag y) →
      (∀ h', Sum.inr h' ∈ Sum.inr h::l → R h' ≠ 0) →
      ∃ t : List (IntAtom I), admissibleIntTail t ∧ (∀ b ∈ t, b.1 ≠ 0) ∧
        ((Sum.inr h::l).map (Sum.elim F R)).prod=integerEval F u none t
    from hx l.length l rfl h hc hnz
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hn h hc hnz
    obtain ⟨k,hk,hku⟩ := (hR h).resolve_left (hnz h (by simp))
    cases l with
    | nil =>
      refine ⟨[(k,none)],⟨by simp,by simp⟩,?_,?_⟩
      · simpa using hk
      · simp [integerEval,wordCoeff,hku]
    | cons x l =>
      cases x with
      | inr h' =>
        have hx := (List.isChain_cons_cons.mp hc).1
        simp [alternatingTag,Sum.elim] at hx
      | inl i =>
        cases l with
        | nil =>
          refine ⟨[(k,some i)],⟨by simp,by simp⟩,?_,?_⟩
          · simpa using hk
          · simp [integerEval,wordCoeff,hku]
        | cons x l =>
          cases x with
          | inl j =>
            have hx := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hc).2).1
            simp [alternatingTag,Sum.elim] at hx
          | inr j =>
            have hcl := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hc).2).2
            obtain ⟨t,ht,hkt,he⟩ := ih l.length (by simp only [List.length_cons] at hn; omega)
              l rfl j hcl (fun h' hh => hnz h' (by simp only [List.mem_cons] at hh ⊢; tauto))
            refine ⟨(k,some i)::t,intTail_cons ht k i,?_,?_⟩
            · intro b hb
              rcases List.mem_cons.mp hb with rfl | hb
              · exact hk
              · exact hkt b hb
            · change R h * (F i * ((Sum.inr j::l).map (Sum.elim F R)).prod)=_
              rw [he,hku]
              simp only [integerEval,wordCoeff,List.map_cons,List.prod_cons,one_mul,mul_assoc]

lemma alternating_moment_zero (τ : M →ₗ[ℂ] ℂ) (F : I → M) (R : H → M) (u : unitary M)
    (hF : ∀ i, τ (F i)=0)
    (hR : ∀ h, R h=0 ∨ ∃ k : ℤ, k ≠ 0 ∧ R h=((u^k : unitary M):M))
    (hm : ∀ a : Option I, ∀ t : List (IntAtom I), admissibleIntTail t →
      (∀ b ∈ t, b.1 ≠ 0) → τ (integerEval F u a t)=0)
    (l : List (I ⊕ H)) (hc : l.IsChain (fun x y => alternatingTag x ≠ alternatingTag y))
    (hl : l ≠ []) : τ ((l.map (Sum.elim F R)).prod)=0 := by
  classical
  by_cases hz : (0:M) ∈ l.map (Sum.elim F R)
  · rw [List.prod_eq_zero hz,map_zero]
  have hnz (h : H) (hh : Sum.inr h ∈ l) : R h ≠ 0 := by
    intro hh0
    exact hz (List.mem_map.mpr ⟨Sum.inr h,hh,hh0⟩)
  cases l with
  | nil => exact (hl rfl).elim
  | cons x l =>
    cases x with
    | inr h =>
      obtain ⟨t,ht,hkt,he⟩ := alternating_right_repr F R u hR h l hc hnz
      rw [he]
      exact hm none t ht hkt
    | inl i =>
      cases l with
      | nil => simpa using hF i
      | cons x l =>
        cases x with
        | inl j =>
          have hx := (List.isChain_cons_cons.mp hc).1
          simp [alternatingTag,Sum.elim] at hx
        | inr h =>
          obtain ⟨t,ht,hkt,he⟩ := alternating_right_repr F R u hR h l
            (List.isChain_cons_cons.mp hc).2 (fun h' hh => hnz h' (by simp only [List.mem_cons] at hh ⊢; tauto))
          change τ (F i * ((Sum.inr h::l).map (Sum.elim F R)).prod)=0
          rw [he]
          have ht' := hm (some i) t ht hkt
          simpa only [integerEval,wordCoeff,one_mul] using ht'
end HochschildPatching

 

 

 

namespace HochschildGradedFree
variable {M G H Q : Type*} [Ring M] [Algebra ℂ M] [Group G] [Group H] [Group Q]
variable (u : G →* M) (v : H →* M) (α : G →* Q) (β : H →* Q)
variable (τ : M →ₗ[ℂ] ℂ)
abbrev Letter := G ⊕ H

def value : Letter (G := G) (H := H) → M := Sum.elim u v
def degreeLetter : Letter (G := G) (H := H) → Q := Sum.elim α β
def tag : Letter (G := G) (H := H) → Bool := Sum.elim (fun _ => false) (fun _ => true)
def evaluate (l : List (Letter (G := G) (H := H))) : M := (l.map (value u v)).prod
def degree (l : List (Letter (G := G) (H := H))) : Q := (l.map (degreeLetter α β)).prod
def centeredValue (x : Letter (G := G) (H := H)) : M := value u v x - τ (value u v x) • (1:M)
def centeredEval (l : List (Letter (G := G) (H := H))) : M := (l.map (centeredValue u v τ)).prod
section
omit [Algebra ℂ M]
@[simp] lemma evaluate_nil : evaluate u v []=1 := rfl
@[simp] lemma evaluate_cons (x : Letter (G := G) (H := H)) (l) :
    evaluate u v (x::l)=value u v x*evaluate u v l := rfl
@[simp] lemma evaluate_append (p q : List (Letter (G := G) (H := H))) :
    evaluate u v (p++q)=evaluate u v p*evaluate u v q := by simp [evaluate,List.prod_append]
end
@[simp] lemma degree_nil : degree α β []=1 := rfl
@[simp] lemma degree_cons (x : Letter (G := G) (H := H)) (l) :
    degree α β (x::l)=degreeLetter α β x*degree α β l := rfl
@[simp] lemma degree_append (p q : List (Letter (G := G) (H := H))) :
    degree α β (p++q)=degree α β p*degree α β q := by simp [degree,List.prod_append]
@[simp] lemma centeredEval_nil : centeredEval u v τ []=1 := rfl
@[simp] lemma centeredEval_cons (x : Letter (G := G) (H := H)) (l) :
    centeredEval u v τ (x::l)=centeredValue u v τ x*centeredEval u v τ l := rfl

lemma degree_rotate_ne_one (x : Letter (G := G) (H := H)) (p q : List (Letter (G := G) (H := H)))
    (hd : degree α β ((x::p)++q) ≠ 1) : degree α β (p++(q++[x])) ≠ 1 := by
  simp only [List.cons_append,degree_cons,degree_append,degree_nil,mul_one] at hd ⊢
  intro hz
  apply hd
  rw [← mul_assoc] at hz
  exact (mul_eq_one_comm.mp hz)

variable (htr : ∀ a b : M, τ (a*b)=τ (b*a))
include htr in
lemma centered_rotate (x : Letter (G := G) (H := H)) (p q : List (Letter (G := G) (H := H))) :
    τ (centeredEval u v τ (x::p)*evaluate u v q)=
      τ (centeredEval u v τ p*evaluate u v (q++[x]))-
        τ (value u v x)*τ (centeredEval u v τ p*evaluate u v q) := by
  simp only [centeredEval_cons,centeredValue,sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,smul_eq_mul]
  congr 1
  rw [mul_assoc,htr]
  simp only [evaluate_append,evaluate_cons,evaluate_nil,mul_one,mul_assoc]

include htr in
lemma partial_center_zero (N : ℕ)
    (hg : ∀ x : Letter (G := G) (H := H), degreeLetter α β x ≠ 1 → τ (value u v x)=0)
    (hs : ∀ l : List (Letter (G := G) (H := H)), l.length<N → degree α β l ≠ 1 → τ (evaluate u v l)=0)
    (p q : List (Letter (G := G) (H := H))) (hn : p.length+q.length<N)
    (hd : degree α β (p++q) ≠ 1) : τ (centeredEval u v τ p*evaluate u v q)=0 := by
  induction p generalizing q with
  | nil => simpa using hs q (by simpa using hn) (by simpa using hd)
  | cons x p ih =>
    rw [centered_rotate u v τ htr]
    have hfirst := ih (q++[x]) (by simp only [List.length_cons,List.length_append,List.length_nil] at hn ⊢; omega)
      (degree_rotate_ne_one α β x p q hd)
    rw [hfirst]
    by_cases hx : τ (value u v x)=0
    · simp [hx]
    · have hgx : degreeLetter α β x=1 := by by_contra h; exact hx (hg x h)
      have hrest : degree α β (p++q) ≠ 1 := by simpa only [List.cons_append,degree_cons,hgx,one_mul] using hd
      rw [ih q (by simp only [List.length_cons] at hn; omega) hrest,mul_zero,sub_zero]

include htr in
lemma partial_center_eq (N : ℕ)
    (hg : ∀ x : Letter (G := G) (H := H), degreeLetter α β x ≠ 1 → τ (value u v x)=0)
    (hs : ∀ l : List (Letter (G := G) (H := H)), l.length<N → degree α β l ≠ 1 → τ (evaluate u v l)=0)
    (p q : List (Letter (G := G) (H := H))) (hn : p.length+q.length=N)
    (hd : degree α β (p++q) ≠ 1) : τ (centeredEval u v τ p*evaluate u v q)=τ (evaluate u v (p++q)) := by
  induction p generalizing q with
  | nil => simp
  | cons x p ih =>
    rw [centered_rotate u v τ htr]
    rw [ih (q++[x]) (by simp only [List.length_cons,List.length_append,List.length_nil] at hn ⊢; omega)
      (degree_rotate_ne_one α β x p q hd)]
    have hzero : τ (value u v x)*τ (centeredEval u v τ p*evaluate u v q)=0 := by
      by_cases hx : τ (value u v x)=0
      · simp [hx]
      · have hgx : degreeLetter α β x=1 := by by_contra h; exact hx (hg x h)
        have hrest : degree α β (p++q) ≠ 1 := by simpa only [List.cons_append,degree_cons,hgx,one_mul] using hd
        rw [partial_center_zero u v α β τ htr N hg hs p q (by simp only [List.length_cons] at hn; omega) hrest,mul_zero]
    rw [hzero,sub_zero]
    simp only [List.cons_append,evaluate_cons,evaluate_append,evaluate_nil,mul_one]
    rw [← mul_assoc,htr]

include htr in
 

theorem moment_eq_zero_of_degree_ne_one
    (hg : ∀ g : G, α g ≠ 1 → τ (u g)=0)
    (hh : ∀ h : H, β h ≠ 1 → τ (v h)=0)
    (hfree : ∀ l : List (Letter (G := G) (H := H)),
      l.IsChain (fun x y => tag x ≠ tag y) → l ≠ [] → τ (centeredEval u v τ l)=0)
    (l : List (Letter (G := G) (H := H))) (hl : degree α β l ≠ 1) :
    τ (evaluate u v l)=0 := by
  classical
  have hletter (x : Letter (G := G) (H := H)) : degreeLetter α β x ≠ 1 → τ (value u v x)=0 := by
    cases x with
    | inl g => exact hg g
    | inr h => exact hh h
  suffices h : ∀ N : ℕ, ∀ k : List (Letter (G := G) (H := H)), k.length=N →
      degree α β k ≠ 1 → τ (evaluate u v k)=0 from h l.length l rfl hl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro k hk hd
    have Hshort (t : List (Letter (G := G) (H := H))) (ht : t.length<k.length)
        (hdt : degree α β t ≠ 1) : τ (evaluate u v t)=0 := ih t.length (hk ▸ ht) t rfl hdt
    by_cases halt : k.IsChain (fun x y => tag x ≠ tag y)
    · have hkc := hfree k halt (fun hn => hd (by simp [hn]))
      have he := partial_center_eq u v α β τ htr k.length hletter Hshort k [] (by simp) (by simpa using hd)
      simpa only [evaluate_nil,mul_one,List.append_nil,hkc] using he.symm
    · rw [List.isChain_iff_forall_rel_of_append_cons_cons] at halt
      push Not at halt
      obtain ⟨a,b,p,q,hk',hab⟩ := halt
      subst k
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          have hz := Hshort (p++Sum.inl (a*b)::q) (by simp)
            (by simpa [degreeLetter,map_mul,mul_assoc] using hd)
          simpa [value,map_mul,mul_assoc] using hz
        | inr b => simp [tag,Sum.elim] at hab
      | inr a =>
        cases b with
        | inl b => simp [tag,Sum.elim] at hab
        | inr b =>
          have hz := Hshort (p++Sum.inr (a*b)::q) (by simp)
            (by simpa [degreeLetter,map_mul,mul_assoc] using hd)
          simpa [value,map_mul,mul_assoc] using hz

end HochschildGradedFree
end

end OAI
