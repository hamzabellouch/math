import Mathlib
import OAI.Computability.FiniteCompiler.Normalization
import OAI.GroupTheory.BooneHigman.TreeCoherence
import OAI.GroupTheory.SimpleOvergroups.EffectiveTables
import OAI.GroupTheory.SimpleOvergroups.FamilyTables

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]

theorem table_zero (C : DelimiterCode A S) (E : FiniteSearch C)
    (wf : WellFounded r) (q : List A → Option Q) (z : S) :
    table C E wf q z 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨u,v⟩ hp
  obtain ⟨w,hw,hn,_,_,_⟩ := (mem_table C E wf q z).mp hp
  exact hn ((C.encode_eq_nil _).mp (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)))
end CodeTable

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

theorem table_zero : table C E wf q z 0 = Base.absorption z := by
  simp [table, CodeTable.table_zero]
end Families

namespace FamilyProgram
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
  [DecidableEq S] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (Q i)]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (z : S) (f : ∀ i, List (A i) → Part (Option (Q i)))

noncomputable def compute (n : ℕ) : Part (List (List S × List S)) :=
  if n = 0 then Part.some (Base.absorption z) else
    (Effect.traverse (fun i => CodedSearch.compute (r := r) (C i) (E i) z (f i) n)
      (Static.letters I)).map (fun rs => Base.absorption z ++ rs.flatten)

omit [∀ index, DecidableEq (A index)] in
@[simp] theorem compute_zero [∀ index, DecidableEq (A index)] :
    compute (r := r) C E z f 0 = Part.some (Base.absorption z) := by
  simp [compute]

variable (wf : WellFounded r) [Std.Trichotomous r]

theorem compute_full {n : ℕ} (q : ∀ i, List (A i) → Option (Q i))
    (h : ∀ i w, (C i |>.encode w).length ≤ n → q i w ∈ f i w) :
    Families.table C E wf q z n ∈ compute (r := r) C E z f n := by
  by_cases hn : n = 0
  · subst n
    simp [compute_zero, Families.table_zero]
  · rw [compute, ite_eq_right hn]
    apply (Part.mem_map_iff _).mpr
    refine ⟨(Static.letters I).map (fun i => CodeTable.table (C i) (E i) wf (q i) z n), ?_, ?_⟩
    · apply Search.traverse_map
      intro i hi
      exact CodedSearch.compute_full (C i) wf (q i) (E i) z (h i)
    · simp only [Families.table, List.flatMap_def]

omit [∀ index, DecidableEq (A index)] [Std.Trichotomous r] in
theorem compute_domain [∀ index, DecidableEq (A index)] [Std.Trichotomous r]
    {n : ℕ} (hn : n ≠ 0)
    (h : (compute (r := r) C E z f n).Dom) :
    ∀ i w, (C i |>.encode w).length ≤ n → (f i w).Dom := by
  rw [compute, ite_eq_right hn] at h
  obtain ⟨out, ho⟩ := Part.dom_iff_mem.mp h
  obtain ⟨rs, hrs, _⟩ := (Part.mem_map_iff _).mp ho
  intro i
  exact CodedSearch.compute_domain (C i) (E i) z
    (Effect.traverse_domain hrs.1 i (by simp [Static.letters]))

theorem compute_eq {n : ℕ} {rs : List (List S × List S)}
    (h : rs ∈ compute (r := r) C E z f n) :
    rs = Families.table C E wf (fun i => Search.value (f i)) z n := by
  by_cases hn : n = 0
  · subst n
    simpa [compute_zero, Families.table_zero] using h
  · exact Part.mem_unique h (compute_full C E z f wf _
      (fun i w hw => Search.value_mem (compute_domain C E z f hn h.1 i w hw)))

include wf

theorem stable {k n : ℕ} (hkn : k ≤ n)
    {rk rn : List (List S × List S)}
    (hk : rk ∈ compute (r := r) C E z f k) (hn : rn ∈ compute (r := r) C E z f n) :
    Selectors.BoundedEq rk rn k := by
  rw [compute_eq C E z f wf hk, compute_eq C E z f wf hn]
  exact Families.stable C E wf _ z hkn

theorem good_zero : GoodTable (r := r) (compute (r := r) C E z f) 0 := by
  refine ⟨Base.absorption z, by simp, ?_, ?_⟩
  · have hh := Families.decreasing C E wf (fun i => Search.value (f i)) z 0
    simpa only [Families.table_zero] using hh
  · constructor
    · intro u u' v v' hu hv x y he hlen
      obtain ⟨a, ha, _⟩ := (Base.mem_absorption z).mp hu
      rcases ha with rfl | rfl <;> simp at hlen
    · intro u u' v v' hu hv p m t hm he hf hlen
      have hml : m.length = 0 := by simp only [List.length_append] at hlen; omega
      exact (hm (List.length_eq_zero_iff.mp hml)).elim

theorem good_at (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet) {n : ℕ}
    (ht : ∀ i w, (C i |>.encode w).length ≤ n → (f i w).Dom)
    (hzero : ∀ i, Search.value (f i) [] ≠ none)
    (hc : ∀ i, CodeTable.Contextual (C i) (Search.value (f i)) n)
    (hi : ∀ i, CodeTable.ZeroIdeal (C i) (Search.value (f i)) n) :
    GoodTable (r := r) (compute (r := r) C E z f) n :=
  ⟨_, compute_full C E z f wf _ (fun i w hw => Search.value_mem (ht i w hw)),
    Families.decreasing C E wf _ z n, Families.critical C E wf _ z hz hd hzero hc hi⟩

theorem bootstrap (normal : List S → Part (List S))
    (fixed : normal = tableNormal (compute (r := r) C E z f))
    (hz : ∀ i, z ∉ (C i).alphabet)
    (hd : ∀ i j, i ≠ j → Disjoint (C i).alphabet (C j).alphabet)
    (bounded : ∀ n, 0 < n → Compiler.PartialBudget normal (3 * (n / 10)) →
      (∀ i w, (C i |>.encode w).length ≤ n → (f i w).Dom) ∧
      (∀ i, Search.value (f i) [] ≠ none) ∧
      (∀ i, CodeTable.Contextual (C i) (Search.value (f i)) n) ∧
      (∀ i, CodeTable.ZeroIdeal (C i) (Search.value (f i)) n)) :
    ∀ n, GoodTable (r := r) (compute (r := r) C E z f) n ∧
      Compiler.PartialBudget normal n := by
  apply bootstrap_length_induction wf _ normal fixed
  · intro k n hkn rk hk rn hn
    exact stable C E z f wf hkn hk hn
  · intro n ih
    by_cases hn : n = 0
    · subst n
      exact good_zero C E z f wf
    · obtain ⟨ht, hzero, hc, hi⟩ := bounded n (Nat.pos_of_ne_zero hn)
        (ih _ (strict_dependency (Nat.pos_of_ne_zero hn)))
      exact good_at C E z f wf hz hd ht hzero hc hi
end FamilyProgram
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
