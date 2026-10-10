import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]
omit [LinearOrder A] in
lemma weight_subperm {as bs : List A} (h : as.Subperm bs) : weight as≤weight bs := by
  obtain ⟨cs,hc,hs⟩:=h
  rw [← weight_perm hc]
  exact weight_sublist hs
lemma weight_finset_subset {s t : Finset A} (h : s⊆t) : weight s≤weight t := by
  apply weight_subperm
  apply (Finset.sort_nodup s (·≤·)).subperm
  intro a ha
  simpa only [Finset.mem_sort] using h (by simpa only [Finset.mem_sort] using ha)
lemma weight_finset_union (s t : Finset A) : weight (s∪t)≤weight s+weight t := by
  have h : (s∪t).sort (·≤·) |>.Subperm (s.sort (·≤·)++t.sort (·≤·)) := by
    apply (Finset.sort_nodup _ _).subperm
    intro a ha
    simpa only [List.mem_append,Finset.mem_sort,Finset.mem_union] using ha
  have hh:=weight_subperm h
  have ha:=weight_append (s.sort (·≤·)) (t.sort (·≤·))
  change weight ((s∪t).sort (·≤·))≤weight (s.sort (·≤·))+weight (t.sort (·≤·))
  omega

namespace FiniteReach
abbrev Input (C A : Type) := (C×Finset A)×Finset A
variable (p : C×(A×A) → Bool)
def grow (x : Input C A) : Finset A :=
  x.2 ∪ x.1.2.filter (fun b=>∃ a∈x.2,p (x.1.1,(a,b))=true)
def sweep (x : Input C A) : Input C A := (x.1,grow p x)
def reach (x : Input C A) : Finset A := (countDown (fun x=>sweep p x.2) x.1.2.card x).2

variable {p}
def neighbor (P : Realizer p) :
    Realizer (fun x : (C×A)×Finset A=>decide (∃ a∈x.2,p (x.1.1,(a,x.1.2))=true)) :=
  finsetAny (composition (pair first.fst (pair second first.snd)) P)
lemma polynomial_neighbor {P : Realizer p} (hP : PolynomialTime P) : PolynomialTime (neighbor P) := by
  unfold neighbor
  exact polynomial_finsetAny (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first)
    (polynomial_pair polynomial_second (polynomial_snd polynomial_first))) hP)

def growRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (grow p) :=
  (composition (pair second (composition (pair (pair first.fst second) first.snd)
    (finsetFilterWith (composition (pair (pair first.fst second) first.snd) (neighbor P))))) (finsetUnion E R)).congr (by
      intro x; ext a; simp only [grow,Function.comp_apply,decide_eq_true_eq])
lemma polynomial_grow {P : Realizer p}
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (growRealizer P E R) := by
  unfold growRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_second (polynomial_composition
    (polynomial_pair (polynomial_pair (polynomial_fst polynomial_first) polynomial_second) (polynomial_snd polynomial_first))
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_pair (polynomial_pair (polynomial_fst polynomial_first) polynomial_second) (polynomial_snd polynomial_first))
      (polynomial_neighbor hP))))) (polynomial_finsetUnion hE hR)

def sweepRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (sweep p) :=
  pair first (growRealizer P E R)
def reachRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (reach p) :=
  composition (composition (pair (composition first.snd finsetCard) identity)
    (iterateDown (composition second (sweepRealizer P E R)))) second

lemma polynomial_reach {P : Realizer p}
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (reachRealizer P E R) := by
  unfold reachRealizer
  apply polynomial_composition _ polynomial_second
  apply polynomial_boundedRepeat
    (polynomial_pair (polynomial_composition (polynomial_snd polynomial_first) polynomial_finsetCard) polynomial_identity)
    (polynomial_composition polynomial_second (polynomial_pair polynomial_first (polynomial_grow hP hE hR)))
    X (3*X+1) (fun x _ z=>z.1=x.1 ∧ z.2⊆x.2∪x.1.2)
  · intro x
    have h:=list_length_le_weight (x.1.2.sort (·≤·))
    rw [Finset.length_sort] at h
    simp only [eval_X,Function.comp_apply]
    change x.1.2.card≤weight x
    change x.1.2.card≤weight ((x.1.1,x.1.2),x.2)
    rw [weight_prod,weight_prod]
    change _≤weight x.1.2 at h
    omega
  · intro x
    exact ⟨rfl,Finset.subset_union_left⟩
  · intro x k hk z ⟨hz,hs⟩
    refine ⟨hz,?_⟩
    change grow p z⊆x.2∪x.1.2
    unfold grow
    apply Finset.union_subset hs
    intro a ha
    exact Finset.mem_union_right _ (hz ▸ (Finset.mem_filter.mp ha).1)
  · intro x k z ⟨hz,hs⟩
    have h1:=weight_finset_subset hs
    have h2:=weight_finset_union x.2 x.1.2
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    change weight z≤3*weight x+1
    change weight (z.1,z.2)≤3*weight (x.1,x.2)+1
    rw [weight_prod z.1 z.2,weight_prod x.1 x.2,hz]
    rw [weight_prod x.1.1 x.1.2]
    omega

omit [Codec A] [Codec C] in
lemma countDown_sweep (x : Input C A) (n : ℕ) :
    countDown (fun x=>sweep p x.2) n x=(x.1,(fun s=>grow p (x.1,s))^[n] x.2) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [countDown,ih]
    simp only [sweep,Function.iterate_succ_apply]

omit [Codec A] [Codec C] in
lemma reach_eq (x : Input C A) : reach p x=(fun s=>grow p (x.1,s))^[x.1.2.card] x.2 := by
  rw [reach,countDown_sweep]
end FiniteReach
end MatchingFPRAS.TreeTyped

end OAI
