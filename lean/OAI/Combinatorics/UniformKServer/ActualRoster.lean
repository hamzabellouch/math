import Mathlib
import OAI.Combinatorics.UniformKServer.ShortRosterValidity
import OAI.Combinatorics.UniformKServer.RosterTails

namespace OAI

                                   
section
namespace UniformKServer.ActualRoster
noncomputable section
attribute [local instance] Classical.propDecidable
open FiniteProbability ChronologicalRoster ShortRoster
variable {I X : Type} [Fintype I] [LinearOrder I] [MetricSpace X]
local instance rosterDecEq : DecidableEq I := fun a b => Classical.propDecidable (a=b)

def survival (K a : ℕ) : ℝ := if a < K^2 then (1-1/(K:ℝ))^(a+1-K) else 0

def valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) : Prop :=
  (∀ ω, D.live ω ⊆ young S c r (K^2)) ∧
    ∀ i, D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) =
      if i ∈ S then survival K (age S c r i) else 0

def active (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) (n i : I) : Prop :=
  dist (c i) (c n) ≤ 20*r ∧ K ≤ age S c r i+1

def compulsory (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ) (i : I) : Prop :=
  K^2 ≤ age S c r i+1

def next (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n : I) : State I where
  Sample := D.Sample × (I → Bool)
  finite := inferInstance
  law := D.law.prod (fresh (1/(K:ℝ)) hq)
  live ω := insert n (retained (active S c r K n) (compulsory S c r K) (D.live ω.1) ω.2)

/-- Only an old selected covering record can trigger this event. The selector
may depend on the entire old roster and its persistent radii, but not on the
fresh lifetime trials. -/
def retires (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (n : I) (select : D.Sample → Option I) (ω : D.Sample) (τ : I → Bool) : Prop :=
  ∃ i, select ω = some i ∧ i ∈ D.live ω ∧
    i ∉ retained (active S c r K n) (compulsory S c r K) (D.live ω) τ
omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem survival_zero (K : ℕ) (hK : 0 < K) : survival K 0 = 1 := by
  simp only [survival,show 0<K^2 by positivity,ite_true,zero_add]
  rw [Nat.sub_eq_zero_of_le hK,pow_zero]

omit [Fintype I] [LinearOrder I] [MetricSpace X] in
theorem survival_step (K a : ℕ) (hK : 2 ≤ K) :
    survival K (a+1) = survival K a *
      (if K ≤ a+1 then (if K^2 ≤ a+1 then 0 else 1-1/(K:ℝ)) else 1) := by
  have hkk : K ≤ K^2 := by nlinarith
  by_cases hcut : K^2 ≤ a+1
  · simp only [survival,not_lt.mpr hcut,ite_false,ite_eq_left (hkk.trans hcut),ite_eq_left hcut,mul_zero]
  · have hay : a < K^2 := by omega
    have hay' : a+1 < K^2 := by omega
    simp only [survival,ite_eq_left hay,ite_eq_left hay',ite_eq_right hcut]
    by_cases htrial : K ≤ a+1
    · rw [ite_eq_left htrial,show a+1+1-K=(a+1-K)+1 by omega,pow_succ]
    · have hzero : a+1-K=0 := by omega
      have hzero' : a+1+1-K=0 := by omega
      simp only [ite_eq_right htrial,hzero,hzero',pow_zero,mul_one]

omit [Fintype I] in
theorem empty_valid (c : I → X) (r : ℝ) (K : ℕ) : valid (State.empty (I := I)) ∅ c r K := by
  constructor
  · intro ω
    exact Finset.empty_subset _
  · intro i
    change (State.empty (I := I)).law.expect (fun _ => if i ∈ (∅:Finset I) then 1 else 0) = _
    simp only [Finset.notMem_empty,ite_false,Law.expect_const]

theorem next_marginal (D : State I) (S : Finset I) (c : I → X) (r : ℝ) (K : ℕ)
    (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n i : I) (hi : i ≠ n) :
    (next D S c r K hq n).law.expect (fun ω => if i ∈ (next D S c r K hq n).live ω then 1 else 0) =
      (if active S c r K n i then (if compulsory S c r K i then 0 else 1-1/(K:ℝ)) else 1)*
        D.law.expect (fun ω => if i ∈ D.live ω then 1 else 0) := by
  change (D.law.prod (fresh (1/(K:ℝ)) hq)).expect (fun ω =>
    if i ∈ insert n (retained (active S c r K n) (compulsory S c r K) (D.live ω.1) ω.2) then 1 else 0) = _
  rw [D.law.expect_prod (fresh (1/(K:ℝ)) hq) (fun ω τ =>
    if i ∈ insert n (retained (active S c r K n) (compulsory S c r K) (D.live ω) τ) then 1 else 0)]
  simp only [Finset.mem_insert,hi,false_or,retained_marginal]
  conv_rhs => rw [←D.law.expect_mul]
  apply D.law.expect_congr
  intro ω
  by_cases hmem : i ∈ D.live ω
  · simp only [ite_eq_left hmem,one_mul,mul_one]
  · simp only [ite_eq_right hmem,zero_mul,mul_zero]
theorem next_valid (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (K : ℕ) (hK : 2 ≤ K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n : I)
    (hD : valid D S c r K) (hn : ∀ i ∈ S, i < n) :
    valid (next D S c r K hq n) (insert n S) c r K := by
  classical
  have hkpos : 0 < K := by omega
  have hkk : K ≤ K^2 := by nlinarith
  rw [insert_linear S n]
  constructor
  · intro ω i hi
    simp only [next,Finset.mem_insert] at hi
    obtain hei | hi := hi
    · subst i
      simp only [young,Finset.mem_filter,Finset.mem_insert_self,true_and]
      rw [new_age_zero S c r n hn]
      positivity
    · have hi' : i ∈ D.live ω.1 ∧
          (¬active S c r K n i ∨ (¬compulsory S c r K i ∧ ω.2 i = true)) := by
        simpa only [retained,Finset.mem_filter] using hi
      obtain ⟨hi,hstay⟩ := hi'
      obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp (hD.1 ω.1 hi)
      simp only [young,Finset.mem_filter,Finset.mem_insert,hiS,or_true,true_and]
      rw [age_insert S c r n i hn hiS]
      by_cases hd : dist (c i) (c n) ≤ 20*r
      · rw [ite_eq_left hd]
        rcases hstay with hstay | hstay
        · change ¬(dist (c i) (c n) ≤ 20*r ∧ K ≤ age S c r i+1) at hstay
          have : age S c r i+1 < K := lt_of_not_ge (fun h => hstay ⟨hd,h⟩)
          omega
        · exact lt_of_not_ge hstay.1
      · simpa only [ite_eq_right hd,add_zero] using hage
  · intro i
    by_cases hi : i = n
    · subst i
      have he : ∀ ω, (if n ∈ (next D S c r K hq n).live ω then (1:ℝ) else 0) = 1 := by
        intro ω
        simp only [next,Finset.mem_insert_self,ite_true]
      rw [Law.expect_congr _ _ _ he,Law.expect_const,new_age_zero S c r n hn]
      simp only [Finset.mem_insert_self,ite_true,survival_zero K hkpos]
    · rw [next_marginal D S c r K hq n i hi,hD.2]
      by_cases hiS : i ∈ S
      · rw [age_insert S c r n i hn hiS]
        simp only [Finset.mem_insert,hiS,or_true,ite_true]
        by_cases hd : dist (c i) (c n) ≤ 20*r
        · simp only [active,hd,true_and,ite_true,compulsory]
          rw [survival_step K (age S c r i) hK]
          ring_nf
        · simp only [active,hd,false_and,ite_false,add_zero,one_mul]
      · simp only [hiS,hi,Finset.mem_insert,false_or,ite_false,mul_zero]
theorem conditional_retirement (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (K : ℕ) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1) (n : I) (p : X)
    (select : D.Sample → Option I)
    (hcover : ∀ ω i, select ω = some i → dist p (c i) ≤ 2*r) (ω : D.Sample) :
    (fresh (I := I) (1/(K:ℝ)) hq).expect (fun τ =>
      if retires D S c r K n select ω τ then 1 else 0) ≤
    1/(K:ℝ)+∑ i : I, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r
      then 1 else 0 := by
  classical
  have hsum : 0 ≤ ∑ i : I, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r
      then (1:ℝ) else 0 := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  cases hsel : select ω with
  | none =>
    have he : ∀ τ, (if retires D S c r K n select ω τ then (1:ℝ) else 0) = 0 := by
      intro τ
      simp [retires,hsel]
    rw [Law.expect_congr _ _ _ he,Law.expect_const]
    linarith [hq.1]
  | some i =>
    have hd := hcover ω i hsel
    have he : ∀ τ, retires D S c r K n select ω τ ↔
        i ∈ D.live ω ∧ i ∉ retained (active S c r K n) (compulsory S c r K) (D.live ω) τ := by
      intro τ
      simp only [retires,hsel,Option.some.injEq,exists_eq_left']
    simp only [he]
    by_cases hi : i ∈ D.live ω
    · by_cases hcp : compulsory S c r K i
      · have hiTerm : (1:ℝ) ≤ ∑ j : I,
            if j ∈ D.live ω ∧ compulsory S c r K j ∧ dist p (c j) ≤ 2*r then 1 else 0 := by
          have hs := Finset.single_le_sum (f := fun j : I =>
            if j ∈ D.live ω ∧ compulsory S c r K j ∧ dist p (c j) ≤ 2*r then (1:ℝ) else 0)
            (s := Finset.univ) (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
          simpa only [hi,hcp,hd,and_self,ite_true] using hs
        have hb := (fresh (I := I) (1/(K:ℝ)) hq).expect_mono
          (fun τ => if i ∈ D.live ω ∧ i ∉ retained (active S c r K n) (compulsory S c r K) (D.live ω) τ then 1 else 0)
          (fun _ => 1) (fun τ => by split_ifs <;> norm_num)
        rw [Law.expect_const] at hb
        linarith [hq.1]
      · by_cases ha : active S c r K n i
        · have hind : ∀ τ, (if i ∈ D.live ω ∧ i ∉ retained (active S c r K n)
              (compulsory S c r K) (D.live ω) τ then (1:ℝ) else 0) = if τ i then 0 else 1 := by
            intro τ
            simp only [retained,Finset.mem_filter,hi,ha,hcp,not_true_eq_false,
              not_false_eq_true,true_and,false_or]
            cases τ i <;> norm_num
          rw [Law.expect_congr _ _ _ hind]
          have hc : (fresh (I := I) (1/(K:ℝ)) hq).expect
              (fun τ => if τ i then 0 else 1) = 1-(1-1/(K:ℝ)) := coins_false _ _ i
          rw [hc]
          linarith
        · have hind : ∀ τ, (if i ∈ D.live ω ∧ i ∉ retained (active S c r K n)
              (compulsory S c r K) (D.live ω) τ then (1:ℝ) else 0) = 0 := by
            intro τ
            simp [retained,hi,ha]
          rw [Law.expect_congr _ _ _ hind,Law.expect_const]
          linarith [hq.1]
    · simp only [hi,false_and,ite_false,Law.expect_const]
      linarith [hq.1]
/-- Source actual-retirement-bound, including arbitrary data-dependent first
coverer and the exact locality cutoff. Survival is averaged over the old law,
not falsely conditioned on a realized surviving old roster. -/
theorem first_retirement (D : State I) (S : Finset I) (c : I → X) (r : ℝ)
    (hr : 0 < r) (K : ℕ) (hK : 2 ≤ K) (hq : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (n : I) (hD : valid D S c r K) (p : X) (select : D.Sample → Option I)
    (hcover : ∀ ω i, select ω = some i → dist p (c i) ≤ 2*r) :
    (D.law.prod (fresh (I := I) (1/(K:ℝ)) hq)).expect (fun ω =>
      if retires D S c r K n select ω.1 ω.2 then 1 else 0) ≤
        if dist (c n) p ≤ 22*r then 49/(K:ℝ) else 0
 := by
  classical
  by_cases hnear : dist (c n) p ≤ 22*r
  · rw [ite_eq_left hnear]
    let C := (young S c r (K^2)).filter fun i => compulsory S c r K i ∧ dist p (c i) ≤ 2*r
    have hC : C ⊆ (young S c r (K^2)).filter fun i => dist p (c i) ≤ 2*r := by
      intro i hi
      obtain ⟨hy,_,hd⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hy,hd⟩
    have hcard : C.card ≤ K^2 := (Finset.card_le_card hC).trans
      (ball_young_count S c r (2*r) (K^2) p (by linarith))
    have hpoint (ω : D.Sample) :
        (fresh (I := I) (1/(K:ℝ)) hq).expect (fun τ =>
          if retires D S c r K n select ω τ then 1 else 0) ≤
        1/(K:ℝ)+∑ i ∈ C, if i ∈ D.live ω then (1:ℝ) else 0 := by
      have hh := conditional_retirement D S c r K hq n p select hcover ω
      have heq : (∑ i : I, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r
            then (1:ℝ) else 0) =
          ∑ i ∈ C, if i ∈ D.live ω ∧ compulsory S c r K i ∧ dist p (c i) ≤ 2*r then 1 else 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ C)
        intro i _ hi
        split_ifs with hp
        · exact (hi (Finset.mem_filter.mpr ⟨hD.1 ω hp.1,hp.2⟩)).elim
        · rfl
      rw [heq] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ D.live ω
      · simp only [ite_eq_left hi]
        split_ifs <;> norm_num
      · simp only [hi,false_and,ite_false,le_refl]
    rw [D.law.expect_prod (fresh (1/(K:ℝ)) hq)
      (fun ω τ => if retires D S c r K n select ω τ then 1 else 0)]
    have hmean := D.law.expect_mono _ _ hpoint
    rw [D.law.expect_add,D.law.expect_const,D.law.expect_finset_sum] at hmean
    have hmarg : ∀ i ∈ C, D.law.expect (fun ω => if i ∈ D.live ω then (1:ℝ) else 0) =
        (1-1/(K:ℝ))^(K^2-K) := by
      intro i hi
      obtain ⟨hy,hcp,_⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiS,hage⟩ := Finset.mem_filter.mp hy
      rw [hD.2 i,ite_eq_left hiS]
      unfold survival
      rw [ite_eq_left hage]
      change K^2 ≤ age S c r i+1 at hcp
      congr 1
      omega
    have hsum : (∑ i ∈ C, D.law.expect (fun ω => if i ∈ D.live ω then (1:ℝ) else 0)) ≤
        (K:ℝ)^2*(1-1/(K:ℝ))^(K^2-K) := by
      rw [Finset.sum_congr rfl hmarg,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ]
      simp only [smul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · exact pow_nonneg (by linarith [hq.2]) _
    exact (hmean.trans (add_le_add le_rfl hsum)).trans (RosterTails.actual_tail K hK)
  · rw [ite_eq_right hnear]
    have he : ∀ ω : D.Sample × (I → Bool),
        (if retires D S c r K n select ω.1 ω.2 then (1:ℝ) else 0) = 0 := by
      intro ω
      apply ite_eq_right
      rintro ⟨i,hsel,hi,hret⟩
      have ha : active S c r K n i := by
        by_contra hn
        exact hret (Finset.mem_filter.mpr ⟨hi,Or.inl hn⟩)
      have hd := hcover ω.1 i hsel
      have ht := dist_triangle (c n) (c i) p
      rw [dist_comm (c n) (c i),dist_comm (c i) p] at ht
      exact hnear (by linarith [ha.1])
    rw [Law.expect_congr _ _ _ he,Law.expect_const]
end
end UniformKServer.ActualRoster

end


end OAI
