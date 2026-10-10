import Mathlib
import OAI.Combinatorics.UniformKServer.ShortRoster

namespace OAI

                                          
section
namespace UniformKServer.ShortRoster
noncomputable section
attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]
local instance rosterDecEq : DecidableEq I := fun a b => Classical.propDecidable (a=b)

/- Finite-set insertion does not depend on the implementation of equality.
This bridge lets the ordered-age lemmas coexist with the canonical classical
finite coin sample space. -/
omit [Fintype I] in
theorem insert_linear (S : Finset I) (n : I) :
    insert n S = @insert I (Finset I)
      (@Finset.instInsert I (fun a b => LinearOrder.toDecidableEq a b)) n S := by
  ext i
  simp only [Finset.mem_insert]

def State.empty : State I where
  Sample := Unit
  finite := inferInstance
  law := ⟨fun _ => 1,by intro; norm_num,by simp⟩
  live _ := ∅

omit [Fintype I] in
theorem State.empty_valid (c : I → X) (r : ℝ) (K : ℕ) (q : ℝ) :
    (State.empty (I := I)).Valid ∅ c r K q := by
  constructor
  · intro ω
    exact Finset.empty_subset _
  · intro i
    change (State.empty (I := I)).law.expect (fun _ => if i ∈ (∅ : Finset I) then 1 else 0) = _
    simp only [Finset.notMem_empty,ite_false,false_and,Law.expect_const]

omit [LinearOrder I] in
theorem retained_marginal (inc kill : I → Prop) (H : Finset I)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (i : I) :
    (fresh (I := I) q hq).expect (fun τ => if i ∈ retained inc kill H τ then 1 else 0) =
      (if i ∈ H then 1 else 0)*(if inc i then (if kill i then 0 else 1-q) else 1) := by
  classical
  by_cases hi : i ∈ H
  · by_cases hc : inc i
    · by_cases hk : kill i
      · simp [retained,hi,hc,hk,Law.expect_const]
      · simp only [retained,Finset.mem_filter,hi,hc,hk,not_true_eq_false,not_false_eq_true,
          true_and,false_or,ite_true,ite_false,one_mul]
        exact coins_true _ _ i
    · simp [retained,hi,hc,Law.expect_const]
  · simp [retained,hi,Law.expect_const]

theorem next_marginal (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n i : I) (hi : i ≠ n) :
    (D.next S c r K q hq n).law.expect (fun ω =>
      if i ∈ (D.next S c r K q hq n).live ω then 1 else 0) =
    (if dist (c i) (c n) ≤ 20*r then (if K ≤ age S c r i+1 then 0 else 1-q) else 1)*
      D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) := by
  change (D.law.prod (fresh q hq)).expect (fun ω =>
    if i ∈ insert n (retained (fun j => dist (c j) (c n) ≤ 20*r)
      (fun j => K ≤ age S c r j+1) (D.live ω.1) ω.2) then 1 else 0) = _
  rw [D.law.expect_prod (fresh q hq) (fun ω τ =>
    if i ∈ insert n (retained (fun j => dist (c j) (c n) ≤ 20*r)
      (fun j => K ≤ age S c r j+1) (D.live ω) τ) then 1 else 0)]
  simp only [Finset.mem_insert,hi,false_or,retained_marginal]
  conv_rhs => rw [←D.law.expect_mul]
  apply D.law.expect_congr
  intro ω
  by_cases hmem : i ∈ D.live ω
  · simp only [ite_eq_left hmem,one_mul,mul_one]
    split_ifs <;> rfl
  · simp only [ite_eq_right hmem,zero_mul,mul_zero]

theorem State.next_valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (K : ℕ) (hK : 0 < K) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : D.Valid S c r K q) (hn : ∀ i ∈ S, i < n) :
    (D.next S c r K q hq n).Valid (insert n S) c r K q := by
  classical
  rw [insert_linear S n]
  constructor
  · intro ω i hi
    simp only [State.next,Finset.mem_insert] at hi
    obtain hei | hi := hi
    · subst i
      simp only [young,Finset.mem_filter,Finset.mem_insert_self,true_and]
      rw [new_age_zero S c r n hn]
      exact hK
    · have hi' : i ∈ D.live ω.1 ∧
          (¬dist (c i) (c n) ≤ 20*r ∨ (¬K ≤ age S c r i+1 ∧ ω.2 i = true)) := by
        simpa only [retained,Finset.mem_filter] using hi
      obtain ⟨hi,hstay⟩ := hi'
      obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp (hD.1 ω.1 hi)
      simp only [young,Finset.mem_filter,Finset.mem_insert,hiS,or_true,true_and]
      rw [age_insert S c r n i hn hiS]
      by_cases hd : dist (c i) (c n) ≤ 20*r
      · rw [ite_eq_left hd]
        exact lt_of_not_ge ((hstay.resolve_left (not_not.mpr hd)).1)
      · simpa only [ite_eq_right hd,add_zero] using hage
  · intro i
    by_cases hi : i = n
    · subst i
      have he : ∀ ω, (if n ∈ (D.next S c r K q hq n).live ω then (1:ℝ) else 0) = 1 := by
        intro ω
        simp only [State.next,Finset.mem_insert_self,ite_true]
      rw [Law.expect_congr _ _ _ he,Law.expect_const,new_age_zero S c r n hn]
      simp only [Finset.mem_insert_self,hK,and_self,ite_true,pow_zero]
    · rw [next_marginal D S c r K q hq n i hi,hD.2]
      by_cases hiS : i ∈ S
      · rw [age_insert S c r n i hn hiS]
        simp only [Finset.mem_insert,hiS,or_true,true_and]
        by_cases hd : dist (c i) (c n) ≤ 20*r
        · rw [ite_eq_left hd,ite_eq_left hd]
          by_cases hk : K ≤ age S c r i+1
          · rw [ite_eq_left hk,ite_eq_right (not_lt.mpr hk),zero_mul]
          · have ha : age S c r i < K := by omega
            rw [ite_eq_right hk,ite_eq_left ha,ite_eq_left (lt_of_not_ge hk),pow_succ]
            exact mul_comm _ _
        · rw [ite_eq_right hd,ite_eq_right hd,add_zero,one_mul]
      · simp only [hiS,hi,Finset.mem_insert,false_or,false_and,ite_false,mul_zero]

end
end UniformKServer.ShortRoster

end

end OAI
