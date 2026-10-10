import Mathlib
import OAI.GroupTheory.FiniteType.HomotopyFunctor
import OAI.GroupTheory.SimpleOvergroups.FamilyTables

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

 theorem table_short {n : ℕ} {p : List S × List S} (hp : p ∈ table C E wf q z n) :
    1 < p.1.length := by
  obtain ⟨w,_,hn,_,he,_⟩ := (mem_table C E wf q z).mp hp
  rw [he]
  have := C.length_le_encode w
  have := List.length_pos_iff.mpr hn
  omega

 theorem canonical_no_infix (hc : ∀ n, Contextual C q n) (hi : ∀ n, ZeroIdeal C q n)
    {w : List A} (hw : q w ≠ none) {n : ℕ} {u v : List S}
    (hp : (u,v) ∈ table C E wf q z n) :
    ¬ u <:+: C.encode (EncodedCanonical.least C wf q w) := by
  obtain ⟨c,_,hcn,hn,rfl,rfl⟩ := (mem_table C E wf q z).mp hp
  rintro ⟨x,y,he⟩
  obtain ⟨a,b,hab,hx,hy⟩ := C.occurrence_decode hcn he.symm
  have hq : q (a++c++b) = q w := hab ▸ EncodedCanonical.least_class C wf q w
  by_cases hz : q c = none
  · exact hw (hq.symm.trans (hi _ a b c le_rfl hz))
  · have hlt : List.Shortlex r (C.encode (EncodedCanonical.least C wf q c)) (C.encode c) := by
      rcases EncodedCanonical.least_lt_or_eq C wf q c with h | h
      · exact h
      · exact False.elim (hn (by simp [output,hz,h]))
    have hb : (C.encode (a++EncodedCanonical.least C wf q c++b)).length ≤
        (C.encode (a++c++b)).length := by
      have hh := EncodedCanonical.least_length C wf q c
      simp only [DelimiterCode.encode_append,List.length_append]
      omega
    have hclass : q (a++EncodedCanonical.least C wf q c++b) = q w :=
      (hc _ a b _ c hb le_rfl (EncodedCanonical.least_class C wf q c)).trans hq
    apply EncodedCanonical.least_global_min C wf q hclass
    rw [hab]
    simpa only [DelimiterCode.encode_append] using shortlex_context hlt (C.encode a) (C.encode b)

 theorem canonical_irreducible {rs : List (List S × List S)} {n : ℕ}
    (hiso : ∀ p ∈ rs, p ∈ table C E wf q z n ∨ ∃ s ∈ p.1, s ∉ C.alphabet)
    (hc : ∀ k, Contextual C q k) (hi : ∀ k, ZeroIdeal C q k)
    {w : List A} (hw : q w ≠ none) :
    Irreducible (Step rs) (C.encode (EncodedCanonical.least C wf q w)) := by
  apply irreducible_of_no_infix
  intro p hp hif
  rcases hiso p hp with hp | ⟨s,hs,hn⟩
  · exact canonical_no_infix C E wf q z hc hi hw hp hif
  · exact hn (C.mem_alphabet_of_mem_encode (hif.subset hs))

 theorem output_eq_iff (hz : z ∉ C.alphabet) (u v : List A) :
    output C wf q z u = output C wf q z v ↔ q u = q v := by
  constructor
  · intro he
    by_cases hu : q u = none <;> by_cases hv : q v = none
    · exact hu.trans hv.symm
    · have hh : z ∈ C.encode (EncodedCanonical.least C wf q v) := by
        rw [output,ite_eq_left hu,output,ite_eq_right hv] at he
        rw [←he]; simp
      exact False.elim (hz (C.mem_alphabet_of_mem_encode hh))
    · have hh : z ∈ C.encode (EncodedCanonical.least C wf q u) := by
        rw [output,ite_eq_right hu,output,ite_eq_left hv] at he
        rw [he]; simp
      exact False.elim (hz (C.mem_alphabet_of_mem_encode hh))
    · rw [output,ite_eq_right hu,output,ite_eq_right hv] at he
      have h := C.encode_injective he
      exact (EncodedCanonical.least_class C wf q u).symm.trans
        ((congrArg q h).trans (EncodedCanonical.least_class C wf q v))
  · exact output_congr C wf q z
end CodeTable

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

 theorem table_short {n : ℕ} {p : List S × List S} (hp : p ∈ table C E wf q z n) :
    1 < p.1.length := by
  classical
  rcases (mem_table C E wf q z).mp hp with hp | ⟨i,hp⟩
  · obtain ⟨a,ha,_⟩ := (Base.mem_absorption z).mp hp
    rcases ha with he | he <;> simp [he]
  · exact CodeTable.table_short (C i) (E i) wf (q i) z hp

 theorem isolate (i : I) (hz : z ∉ (C i).alphabet)
    (hd : ∀ j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet)
    {n : ℕ} {p : List S × List S} (hp : p ∈ table C E wf q z n) :
    p ∈ CodeTable.table (C i) (E i) wf (q i) z n ∨ ∃ s ∈ p.1, s ∉ (C i).alphabet := by
  classical
  rcases (mem_table C E wf q z).mp hp with hp | ⟨j,hp⟩
  · obtain ⟨a,ha,_⟩ := (Base.mem_absorption z).mp hp
    exact Or.inr ⟨z,by rcases ha with he | he <;> simp [he],hz⟩
  · by_cases he : i = j
    · subst j; exact Or.inl hp
    · obtain ⟨w,_,hn,_,hl,_⟩ := (CodeTable.mem_table (C j) (E j) wf (q j) z).mp hp
      have hw : (C j).encode w ≠ [] := mt ((C j).encode_eq_nil _).mp hn
      obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hw
      exact Or.inr ⟨s,hl ▸ hs,fun h => Set.disjoint_left.mp (hd j he) h
        ((C j).mem_alphabet_of_mem_encode hs)⟩
end Families

namespace CodeQuotient
open FiniteAlgebraicEnvelopes.Bootstrap.Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {t : S → S → Prop} (wt : WellFounded t)
  (good : ∀ n, GoodTable (r:=t) T n)
  (stable : ∀ k n, k ≤ n → ∀ rk ∈ T k, ∀ rn ∈ T n, Selectors.BoundedEq rk rn k)
variable {A Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)
variable (hshort : ∀ n rs, rs ∈ T n → ∀ p ∈ rs, 1 < p.1.length)
variable (hiso : ∀ n rs, rs ∈ T n → ∀ p ∈ rs,
  p ∈ CodeTable.table C E wf q z n ∨ ∃ s ∈ p.1, s ∉ C.alphabet)
variable (hstatic : ∀ n rs, rs ∈ T n → ∀ p ∈ CodeTable.table C E wf q z n, p ∈ rs)
variable (hc : ∀ n, CodeTable.Contextual C q n) (hi : ∀ n, CodeTable.ZeroIdeal C q n)
  (hzero : q [] ≠ none)
include wt good stable hshort hiso hstatic hc hi hzero

 theorem normal_encode (w : List A) : normal T (C.encode w) = CodeTable.output C wf q z w := by
  have hfixed : normal T (CodeTable.output C wf q z w) = CodeTable.output C wf q z w := by
    by_cases hq : q w = none
    · rw [CodeTable.output,ite_eq_left hq]
      obtain ⟨rs,hrs,_⟩ := good 1
      exact normal_eq_self T wt good stable hrs
        (irreducible_of_short (fun p hp => hshort 1 rs hrs p hp))
    · rw [CodeTable.output,ite_eq_right hq]
      obtain ⟨rs,hrs,_⟩ := good (C.encode (EncodedCanonical.least C wf q w)).length
      exact normal_eq_self T wt good stable hrs
        (CodeTable.canonical_irreducible C E wf q z (hiso _ rs hrs) hc hi hq)
  have hpres : present T (C.encode w) = present T (CodeTable.output C wf q z w) := by
    obtain ⟨rs,hrs,hd,_⟩ := good (C.encode w).length
    exact present_steps T hrs hd le_rfl
      (steps_mono (hstatic _ rs hrs) (CodeTable.whole_steps C E wf q z hzero le_rfl))
  exact ((present_eq_iff T wt good stable _ _).mp hpres).trans hfixed

 theorem present_encode_iff (hz : z ∉ C.alphabet) (u v : List A) :
    present T (C.encode u) = present T (C.encode v) ↔ q u = q v := by
  rw [present_eq_iff T wt good stable,
    normal_encode T wt good stable C E wf q z hshort hiso hstatic hc hi hzero,
    normal_encode T wt good stable C E wf q z hshort hiso hstatic hc hi hzero]
  exact CodeTable.output_eq_iff C wf q z hz u v
end CodeQuotient

namespace CodeQuotient
open FiniteAlgebraicEnvelopes.Bootstrap.Quotient
variable {A S M : Type*} [DecidableEq S] [Monoid M]
variable {T : ℕ → Part (List (List S × List S))}
variable (C : DelimiterCode A S)

def codeHom : FreeMonoid A →* Mon T where
  toFun w := present T (C.encode w.toList)
  map_one' := by simp
  map_mul' u v := by simp only [FreeMonoid.toList_mul,DelimiterCode.encode_append,present_append]

variable (e : FreeMonoid A →* M) (he : Function.Surjective e)
  (hc : ∀ u v : List A,present T (C.encode u)=present T (C.encode v) ↔
    e (FreeMonoid.ofList u)=e (FreeMonoid.ofList v))

noncomputable def descendCode : M →* Mon T where
  toFun x := codeHom C (he x).choose
  map_one' := by
    have hx : e (he 1).choose=e 1 := (he 1).choose_spec.trans e.map_one.symm
    exact (hc _ []).mpr hx
  map_mul' x y := by
    change present T (C.encode ((he (x*y)).choose.toList)) =
      present T (C.encode ((he x).choose.toList))*present T (C.encode ((he y).choose.toList))
    rw [←present_append,←DelimiterCode.encode_append]
    apply (hc _ _).mpr
    change e (he (x*y)).choose=e ((he x).choose * (he y).choose)
    rw [e.map_mul,(he (x*y)).choose_spec,(he x).choose_spec,(he y).choose_spec]

omit [DecidableEq S] in
theorem descendCode_apply (w : List A) :
    descendCode C e he hc (e (FreeMonoid.ofList w))=present T (C.encode w) :=
  (hc _ w).mpr (he (e (FreeMonoid.ofList w))).choose_spec

omit [DecidableEq S] in
theorem descendCode_injective : Function.Injective (descendCode C e he hc) := by
  intro x y h
  exact (he x).choose_spec.symm.trans (((hc _ _).mp h).trans (he y).choose_spec)
end CodeQuotient
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
