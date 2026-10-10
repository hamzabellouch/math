import Mathlib
import OAI.Combinatorics.KServer.Tiers

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open RosterLifetimes FiniteBallLaw PartitionProbabilities Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

lemma final_survival {K a : ℕ} (hK : 2 ≤ K) (ha : a+1=K^2) :
    actualPresence K a=survive (1/(K:ℝ)) (K^2-K) := by
  have hkk : K+1 ≤ K^2 := by nlinarith
  have hak : ¬a<K := by omega
  have hac : a<K^2 := by omega
  have he : a-K+1=K^2-K := by omega
  simp only [actualPresence,ite_eq_right hak,ite_eq_left hac,he]

/-- Unconditional marginal death bound. The extra tail is never interpreted
as a conditional compulsory hazard. -/
lemma death_marginal {K a b : ℕ} (hK : 2 ≤ K) (hab : a ≤ b) (hba : b ≤ a+1) :
    (∑ d : Lifetime K, if alive K a d ∧ ¬alive K b d then lifetimeLaw K d else 0) ≤
      (1/(K:ℝ))*actualPresence K a+
        if a<K^2 then survive (1/(K:ℝ)) (K^2-K) else 0 := by
  have hk : 1≤K := by omega
  have hq := (rate_range hk).1
  have hs := (survival_range hk a).1
  have ht := (survive_range (rate_range hk) (K^2-K)).1
  by_cases he : b=a
  · subst b
    simp only [and_not_self,ite_false,sum_const_zero]
    exact add_nonneg (mul_nonneg hq hs) (by split_ifs <;> positivity)
  · have hb : b=a+1 := by omega
    subst b
    rw [death_probability hk]
    by_cases hac : a<K^2
    · rw [ite_eq_left hac]
      by_cases hbc : a+1<K^2
      · exact (ordinary_death_bound hk hbc).trans (le_add_of_nonneg_right ht)
      · have heq : a+1=K^2 := by omega
        rw [actual_cutoff (a:=a+1) (by omega),sub_zero,final_survival hK heq]
        exact le_add_of_nonneg_left (mul_nonneg hq ht)
    · rw [ite_eq_right hac,actual_cutoff (le_of_not_gt hac),actual_cutoff (by omega)]
      simp

/-- A literal finite lifetime-tape first-coverer estimate.  The `S` hypothesis
is only a deterministic candidate count, and is discharged by chronological
ages below. -/
theorem first_retirement_bound {H K : ℕ} (hK : 2 ≤ K)
    (a b : Fin H → ℕ) (inc : ∀ i, a i≤b i ∧ b i≤a i+1)
    (cover : Fin H → Prop) (S : Finset (Fin H))
    (hS : ∀ i, cover i → a i<K^2 → i∈S) (hcard : S.card ≤ K^2) :
    PartitionProbabilities.probability (fun _ : Fin H=>lifetimeLaw K)
      (firstSeparation (fun i d=>cover i ∧ alive K (a i) d)
        (fun i d=>cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d)) ≤ 49/(K:ℝ) := by
  have hk : 1≤K := by omega
  have hkp : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  let T : ℝ := survive (1/(K:ℝ)) (K^2-K)
  have hT : 0≤T := (survive_range (rate_range hk) _).1
  let ε : Fin H → ℝ := fun i=>if i∈S then (K:ℝ)*T else 0
  have heps : ∑ i, ε i=(K:ℝ)*T*S.card := by simp [ε,sum_ite_mem,mul_comm]
  have hh := SparseFirstHit.sparse_bound (fun _ : Fin H=>lifetimeLaw K)
    (fun _=>lifetime_nonneg hk) (fun _=>lifetime_sum hk)
    (hit:=fun i d=>cover i ∧ alive K (a i) d)
    (sep:=fun i d=>cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d)
    (fun _ _ h=>⟨h.1,h.2.1⟩) ε (rate_range hk).1
    (fun i=>by dsimp [ε]; split_ifs <;> positivity)
  have hm (i : Fin H) : (∑ d, if cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d then lifetimeLaw K d else 0) ≤
      (1/(K:ℝ))*((∑ d, if cover i ∧ alive K (a i) d then lifetimeLaw K d else 0)+ε i) := by
    by_cases hc : cover i
    · simp only [hc,true_and]
      rw [alive_probability hk]
      have hd := death_marginal hK (inc i).1 (inc i).2
      refine hd.trans ?_
      by_cases hy : a i<K^2
      · simp only [ite_eq_left hy,ε,ite_eq_left (hS i hc hy)]
        dsimp [T]
        field_simp
        exact le_rfl
      · simp only [ite_eq_right hy,add_zero]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by dsimp [ε]; split_ifs <;> positivity)) (rate_range hk).1
    · simp only [hc,false_and,ite_false,sum_const_zero,zero_add]
      exact mul_nonneg (rate_range hk).1 (by dsimp [ε]; split_ifs <;> positivity)
  have hb := hh (fun i=>by
    convert hm i using 1
    · apply sum_congr rfl
      intro d _
      by_cases h : cover i ∧ alive K (a i) d ∧ ¬alive K (b i) d <;> simp [h]
    · apply congrArg (fun z : ℝ=>(1/(K:ℝ))*(z+ε i))
      apply sum_congr rfl
      intro d _
      by_cases h : cover i ∧ alive K (a i) d <;> simp [h])
  rw [heps] at hb
  have hc : (S.card:ℝ)≤(K:ℝ)^2 := by exact_mod_cast hcard
  have hfin : (1/(K:ℝ))*(1+(K:ℝ)*T*S.card) ≤ 1/(K:ℝ)+(K:ℝ)^2*T := by
    calc _ ≤ (1/(K:ℝ))*(1+(K:ℝ)*T*(K:ℝ)^2) := by gcongr
         _ = _ := by field_simp
  exact (hb.trans hfin).trans (actual_retirement_bound K hK)

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

/-- The unconditional first-coverer retirement estimate for an actual fixed
chronological roster and arbitrary fixed radii. Increment bounds follow from
one chronological insertion, not from the realized random presences. -/
theorem chronological_retirement_bound (center : ℕ → Y) (I : Finset ℕ)
    {r : ℝ} (hr : 0 < r) (hK : 2≤K) (rad : Fin H → Outcome Y r) (p : Y)
    (b : Fin H → ℕ) (hinc : ∀ i : Fin H, age center I (20*r) i≤b i ∧ b i≤age center I (20*r) i+1) :
    PartitionProbabilities.probability (fun _ : Fin H=>lifetimeLaw K)
      (firstSeparation
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i) ∧ alive K (age center I (20*r) i) d)
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i) ∧
          alive K (age center I (20*r) i) d ∧ ¬alive K (b i) d)) ≤49/(K:ℝ) := by
  let a : Fin H → ℕ := fun i=>age center I (20*r) i
  let pres : Fin H → Prop := fun i=>(i:ℕ)∈I ∧ a i<K^2
  let S := SparseFirstHit.candidates r (fun i : Fin H=>center i) pres p p
  have hb := first_retirement_bound hK a b hinc
    (fun i=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i)) S
    (fun i hi ha=>by
      simp only [S,SparseFirstHit.candidates,mem_filter,mem_univ,true_and,min_self]
      exact ⟨⟨hi.1,ha⟩,hi.2.trans (radius_range hr _).2⟩)
    (SparseFirstHit.candidate_count hr.le center I pres (fun _ h=>h) p p (by simpa using hr.le))
  simpa only [a,and_assoc] using hb

end KServer.ActualRoster

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

omit [Fintype Y] in
lemma age_insert_bounds (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (t i : ℕ) :
    age center I R i ≤ age center (insert t I) R i ∧
      age center (insert t I) R i ≤ age center I R i+1 := by
  refine ⟨age_mono center (subset_insert _ _) le_rfl i,?_⟩
  unfold age
  rw [filter_insert]
  split_ifs
  · exact card_insert_le _ _
  · omega

lemma old_covered_of_new (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) (i : Fin H)
    (hit : (i:ℕ)≠t) (hi : covered center (insert t I) r life rad p i) :
    covered center I r life rad p i := by
  refine ⟨⟨(mem_insert.mp hi.1.1).resolve_left hit,?_⟩,hi.2⟩
  exact alive_antitone K _ (age_insert_bounds center I (20*r) t i).1 hi.1.2

lemma new_covered_of_persists (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) (i : Fin H)
    (hi : covered center I r life rad p i) (hp : present center (insert t I) r life i) :
    covered center (insert t I) r life rad p i := ⟨hp,hi.2⟩

/-- Chronological appending cannot supersede a surviving first coverer. -/
lemma first_persists (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r)
    (p : Y) (i : Fin H) (hfirst : first center I r life rad p=some i)
    (hp : present center (insert t I) r life i) :
    first center (insert t I) r life rad p=some i := by
  obtain ⟨hc,hbefore⟩ := (first_some_iff _ _ _ _ _ _ _).mp hfirst
  apply (first_some_iff _ _ _ _ _ _ _).mpr
  refine ⟨new_covered_of_persists center I r t life rad p i hc hp,?_⟩
  intro j hj hnew
  have hji : (j:ℕ) < i := hj
  have hit := hI i hc.1.1
  exact hbefore j hj (old_covered_of_new center I r t life rad p j (by omega) hnew)

def retired (center : ℕ → Y) (I J : Finset ℕ) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) : Prop :=
  ∃ i, first center I r life rad p=some i ∧ ¬present center J r life i

lemma retired_iff (center : ℕ → Y) (I J : Finset ℕ) (hIJ : I⊆J) (r : ℝ)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) :
    retired center I J r life rad p ↔
      firstSeparation
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i) ∧ alive K (age center I (20*r) i) d)
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i) ∧
          alive K (age center I (20*r) i) d ∧ ¬alive K (age center J (20*r) i) d) life := by
  constructor
  · rintro ⟨i,hf,hn⟩
    obtain ⟨hi,hbef⟩ := (first_some_iff _ _ _ _ _ _ _).mp hf
    refine ⟨i,⟨hi.1.1,hi.2,hi.1.2,fun h=>hn ⟨hIJ hi.1.1,h⟩⟩,?_⟩
    rintro j hj ⟨hm,hd,ha⟩
    exact hbef j hj ⟨⟨hm,ha⟩,hd⟩
  · rintro ⟨i,⟨hm,hd,ha,hn⟩,hbef⟩
    refine ⟨i,(first_some_iff _ _ _ _ _ _ _).mpr ⟨⟨⟨hm,ha⟩,hd⟩,?_⟩,fun h=>hn h.2⟩
    intro j hj hh
    exact hbef j hj ⟨hh.1.1,hh.2,hh.1.2⟩

/-- An actual insertion's exceptional first-coverer retirement row, under the
literal lifetime tape and with every radius held fixed. -/
theorem insertion_retirement (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0<r)
    (hK : 2≤K) (t : ℕ) (rad : Fin H → Outcome Y r) (p : Y) :
    PartitionProbabilities.probability (fun _ : Fin H=>lifetimeLaw K)
      (fun life=>retired center I (insert t I) r life rad p) ≤49/(K:ℝ) := by
  have he : (fun life=>retired center I (insert t I) r life rad p)=
      firstSeparation
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i) ∧ alive K (age center I (20*r) i) d)
        (fun i d=>(i:ℕ)∈I ∧ dist (center i) p≤radius r (rad i) ∧
          alive K (age center I (20*r) i) d ∧ ¬alive K (age center (insert t I) (20*r) i) d) := by
    funext life
    exact propext (retired_iff center I _ (subset_insert _ _) r life rad p)
  rw [he]
  exact chronological_retirement_bound center I hr hK rad p _ (fun i=>age_insert_bounds center I (20*r) t i)

/-- The retirement error is supported inside the 22r neighbourhood. -/
lemma retired_near (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0<r) (t : ℕ)
    (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r)
    (p : Y) (h : retired center I (insert t I) r life rad p) : dist p (center t)≤22*r := by
  obtain ⟨i,hf,hn⟩ := h
  obtain ⟨hi,_⟩ := (first_some_iff _ _ _ _ _ _ _).mp hf
  have hit : (i:ℕ)<t := hI i hi.1.1
  have ht : t∉I := fun hh=>Nat.lt_irrefl _ (hI t hh)
  have hc : dist (center i) (center t)≤20*r := by
    by_contra hc
    have ha := age_insert center I (20*r) ht hit
    rw [ite_eq_right hc,add_zero] at ha
    apply hn
    exact ⟨mem_insert_of_mem hi.1.1,ha ▸ hi.1.2⟩
  have hp := hi.2.trans (radius_range hr _).2
  have htri := dist_triangle p (center i) (center t)
  rw [dist_comm p (center i)] at htri
  linarith

/-- A fresh appended ball covers every point within r, pathwise even on
zero-probability lifetime tape outcomes. -/
lemma inserted_covers (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0<r) (hK : 0<K)
    (t : Fin H) (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K)
    (rad : Fin H → Outcome Y r) (p : Y) (hp : dist (center t) p≤r) :
    covered center (insert (t:ℕ) I) r life rad p t := by
  refine ⟨⟨mem_insert_self _ _,?_⟩,hp.trans (radius_range hr _).1⟩
  rw [age_new center I (20*r) hI]
  exact alive_certain hK _

def indicator (P : Prop) : ℝ := if P then 1 else 0

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num at *
lemma indicator_le_one (P : Prop) : indicator P≤1 := by unfold indicator; split_ifs <;> norm_num at *

/-- Literal stationary noncoverage table. -/
theorem stationary_table (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (t : ℕ)
    (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (p : Y) :
    indicator (first center I r life rad p≠first center (insert t I) r life rad p)+
      indicator (first center (insert t I) r life rad p=none)-
      indicator (first center I r life rad p=none) ≤
        2*indicator (retired center I (insert t I) r life rad p) := by
  cases ho : first center I r life rad p with
  | none =>
    cases hn : first center (insert t I) r life rad p with
    | none => simp only [indicator]; split_ifs <;> norm_num at *
    | some j => simp only [indicator]; split_ifs <;> norm_num at *
  | some i =>
    by_cases hr : retired center I (insert t I) r life rad p
    · rw [show indicator (retired center I (insert t I) r life rad p)=1 from ite_eq_left hr]
      cases hn : first center (insert t I) r life rad p with
      | none => unfold indicator; split_ifs <;> norm_num at *
      | some j => simp only [indicator]; split_ifs <;> norm_num at *
    · have hp : present center (insert t I) r life i := by
        by_contra hp; exact hr ⟨i,ho,hp⟩
      have hn := first_persists center I r t hI life rad p i ho hp
      simp [hn,indicator,hr]

/-- Mover row, using final guaranteed coverage instead of a stationary final
position. Its retirement coefficient is one instead of two. -/
theorem mover_table (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0<r) (hK : 0<K)
    (t : Fin H) (hI : ∀ i∈I, i<t) (life : Fin H → Lifetime K)
    (rad : Fin H → Outcome Y r) (p : Y) :
    indicator (first center I r life rad p≠first center (insert (t:ℕ) I) r life rad p)+
      indicator (first center (insert (t:ℕ) I) r life rad (center t)=none)-
      indicator (first center I r life rad p=none) ≤
        indicator (retired center I (insert (t:ℕ) I) r life rad p) := by
  have hc := inserted_covers center I hr hK t hI life rad (center t) (by simpa using hr.le)
  have hn : first center (insert (t:ℕ) I) r life rad (center t)≠none :=
    fun h=>(first_none_iff _ _ _ _ _ _).mp h t hc
  rw [show indicator (first center (insert (t:ℕ) I) r life rad (center t)=none)=0 from ite_eq_right hn,add_zero]
  cases ho : first center I r life rad p with
  | none =>
    unfold indicator
    split_ifs <;> norm_num at *
  | some i =>
    by_cases he : retired center I (insert (t:ℕ) I) r life rad p
    · rw [show indicator (retired center I (insert (t:ℕ) I) r life rad p)=1 from ite_eq_left he]
      unfold indicator
      split_ifs <;> norm_num at *
    · have hp : present center (insert (t:ℕ) I) r life i := by
        by_contra hp; exact he ⟨i,ho,hp⟩
      have hnew := first_persists center I r t hI life rad p i ho hp
      simp [hnew,indicator,he]

end KServer.ActualRoster

end


/-! One-structure edits of the actual priority map. These lemmas keep earlier
structures fixed; in particular a covered heavy key suppresses all tier edits. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y:Type*} [Fintype I] [LinearOrder I] {A:I→Type*}

lemma selected_congr_point (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y)
    (h:∀ i,q₀ i x=q₁ i x) : selected q₀ x=selected q₁ x := by
  let u₀:(i:I)→Unit→Option (A i):=fun i _=>q₀ i x
  let u₁:(i:I)→Unit→Option (A i):=fun i _=>q₁ i x
  have hu:u₀=u₁:=funext fun i=>funext fun _=>h i
  change selected u₀ ()=selected u₁ ()
  rw [hu]

lemma key_congr_point (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y)
    (h:∀ i,q₀ i x=q₁ i x) : key q₀ x=key q₁ x := by
  simp only [key,selected_congr_point q₀ q₁ x h]

lemma key_ne_single (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y) (j:I)
    (h:∀ i,i≠j→q₀ i x=q₁ i x) (hn:key q₀ x≠key q₁ x) : q₀ j x≠q₁ j x := by
  intro he
  apply hn
  apply key_congr_point
  intro i
  by_cases hi:i=j
  · subst i; exact he
  · exact h i hi

lemma single_indicator (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y) (j:I)
    (h:∀ i,i≠j→q₀ i x=q₁ i x) :
    ActualRoster.indicator (key q₀ x≠key q₁ x) ≤ ActualRoster.indicator (q₀ j x≠q₁ j x) := by
  unfold ActualRoster.indicator
  split_ifs with hn hj hj <;> try norm_num
  exact False.elim (hj (key_ne_single q₀ q₁ x j h hn))

/-- Before and after the elementary edit at structure j. -/
def stageBefore (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) : (i:I)→Y→Option (A i) :=
  fun i=>if i<j then q₁ i else q₀ i

def stageAfter (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) : (i:I)→Y→Option (A i) :=
  fun i=>if i≤j then q₁ i else q₀ i

omit [Fintype I] in
lemma stage_at (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) :
    stageBefore q₀ q₁ j j=q₀ j ∧ stageAfter q₀ q₁ j j=q₁ j := by
  simp [stageBefore,stageAfter]

omit [Fintype I] in
lemma stage_outside (q₀ q₁:(i:I)→Y→Option (A i)) (j i:I) (hi:i≠j) :
    stageBefore q₀ q₁ j i=stageAfter q₀ q₁ j i := by
  simp only [stageBefore,stageAfter,le_iff_lt_or_eq,hi,or_false]

lemma stage_charge (q₀ q₁:(i:I)→Y→Option (A i)) (j:I) (x:Y) :
    ActualRoster.indicator (key (stageBefore q₀ q₁ j) x≠key (stageAfter q₀ q₁ j) x) ≤
      ActualRoster.indicator (q₀ j x≠q₁ j x) := by
  have h:=single_indicator (stageBefore q₀ q₁ j) (stageAfter q₀ q₁ j) x j
    (fun i hi=>congrFun (stage_outside q₀ q₁ j i hi) x)
  simpa only [(stage_at q₀ q₁ j).1,(stage_at q₀ q₁ j).2] using h

variable [OrderBot I]

lemma selected_bot (q:(i:I)→Y→Option (A i)) (x:Y) (a:A ⊥) (ha:q ⊥ x=some a) :
    selected q x=some ⟨⊥,a⟩ := by
  have hc:(covered q x).Nonempty:=⟨⊥,mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩⟩
  have he:(covered q x).min' hc=⊥:=bot_unique (min'_le (covered q x) ⊥ (mem_filter.mpr ⟨mem_univ _,by rw [ha]; exact Option.some_ne_none _⟩))
  unfold selected
  rw [dite_eq_left hc]
  change (q ((covered q x).min' hc) x).map (fun b=>(⟨(covered q x).min' hc,b⟩:Sigma A))=some ⟨⊥,a⟩
  rw [he,ha]
  rfl

lemma key_bot (q:(i:I)→Y→Option (A i)) (x:Y) (a:A ⊥) (ha:q ⊥ x=some a) :
    key q x=Sum.inl ⟨⊥,a⟩ := by simp only [key,selected_bot q x a ha]

lemma bot_shadow (q₀ q₁:(i:I)→Y→Option (A i)) (x:Y) (a:A ⊥)
    (h₀:q₀ ⊥ x=some a) (h₁:q₁ ⊥ x=some a) : key q₀ x=key q₁ x :=
  (key_bot q₀ x a h₀).trans (key_bot q₁ x a h₁).symm
lemma stage_shadow (q₀ q₁:(i:I)→Y→Option (A i)) {j:I} (hj:⊥<j)
    (x:Y) (a:A ⊥) (ha:q₁ ⊥ x=some a) :
    key (stageBefore q₀ q₁ j) x=key (stageAfter q₀ q₁ j) x := by
  apply bot_shadow _ _ x a
  · simpa only [stageBefore,ite_eq_left hj] using ha
  · simpa only [stageAfter,ite_eq_left hj.le] using ha
end KServer.PriorityKeys

end


/-! Literal finite-label tier edit tables. The old/new difference is bounded
through permanent chronological labels; no resampling or independence is
assumed at an observed surviving roster. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierEdits
open ActualRoster Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

lemma indicator_mono {P Q:Prop} (h:P→Q) : indicator P≤ indicator Q := by
  unfold indicator
  split_ifs with hP hQ hQ <;> try norm_num
  exact False.elim (hQ (h hP))

lemma map_charge {A B:Type*} (f:A→B) (a b:Option A) :
    indicator (a.map f≠b.map f)≤ indicator (a≠b) :=
  indicator_mono (fun hn he=>hn (congrArg (Option.map f) he))

lemma map_none {A B:Type*} (f:A→B) (a:Option A) :
    indicator (a.map f=none)=indicator (a=none) := by
  cases a <;> simp [indicator]

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {H K:ℕ}

lemma key_none (center:ℕ→Y) {r:ℝ} (hr:0≤r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y) :
    indicator (TierKeys.key center hr K q life rad t p=none)=
      indicator (first center (schedule center r K q t) r life rad p=none) :=
  map_none _ _

lemma key_change (center:ℕ→Y) {r:ℝ} (hr:0≤r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y) :
    indicator (TierKeys.key center hr K q life rad t p≠TierKeys.key center hr K q life rad (t+1) p)≤
      indicator (first center (schedule center r K q t) r life rad p≠
        first center (schedule center r K q (t+1)) r life rad p) :=
  map_charge _ _ _

lemma stationary (center:ℕ→Y) {r:ℝ} (hr:0≤r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ) (p:Y)
    (hin:insertTest center (schedule center r K q t) r K t (q t)) :
    indicator (TierKeys.key center hr K q life rad t p≠TierKeys.key center hr K q life rad (t+1) p)+
      indicator (TierKeys.key center hr K q life rad (t+1) p=none)-
      indicator (TierKeys.key center hr K q life rad t p=none) ≤
        2*indicator (retired center (schedule center r K q t) (schedule center r K q (t+1)) r life rad p) := by
  have ht:=stationary_table center (schedule center r K q t) r t (schedule_before _ _ _ _ _) life rad p
  have hnew:schedule center r K q (t+1)=insert t (schedule center r K q t):=by
    simp only [schedule,ite_eq_left hin]
  have hc:=key_change center hr q life rad t p
  rw [key_none,key_none,hnew]
  rw [hnew] at hc
  linarith

lemma mover (center:ℕ→Y) {r:ℝ} (hr:0<r) (hK:0<K) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:Fin H) (p:Y)
    (hin:insertTest center (schedule center r K q t) r K t (q t)) :
    indicator (TierKeys.key center hr.le K q life rad t p≠TierKeys.key center hr.le K q life rad (t.val+1) p)+
      indicator (TierKeys.key center hr.le K q life rad (t.val+1) (center t)=none)-
      indicator (TierKeys.key center hr.le K q life rad t p=none) ≤
        indicator (retired center (schedule center r K q t) (schedule center r K q (t.val+1)) r life rad p) := by
  have ht:=mover_table center (schedule center r K q t) hr hK t (schedule_before _ _ _ _ _) life rad p
  have hnew:schedule center r K q (t.val+1)=insert (t:ℕ) (schedule center r K q t):=by
    simp only [schedule,ite_eq_left hin]
  have hc:=key_change center hr.le q life rad t p
  rw [key_none,key_none,hnew]
  rw [hnew] at hc
  linarith

lemma no_insert (center:ℕ→Y) {r:ℝ} (hr:0≤r) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:ℕ)
    (hin:¬insertTest center (schedule center r K q t) r K t (q t)) :
    TierKeys.key center hr K q life rad (t+1)=TierKeys.key center hr K q life rad t := by
  funext p
  simp only [TierKeys.key,schedule,ite_eq_right hin]

lemma covered_inner (center:ℕ→Y) {r:ℝ} (hr:0<r) (hK:0<K) (q:ℕ→Prop)
    (life:Fin H→Lifetime K) (rad:Fin H→FiniteBallLaw.Outcome Y r) (t:Fin H)
    (hin:insertTest center (schedule center r K q t) r K t (q t)) (p:Y) (hp:dist (center t) p≤r) :
    indicator (TierKeys.key center hr.le K q life rad (t.val+1) p=none)=0 := by
  rw [key_none]
  have hnew:schedule center r K q (t.val+1)=insert (t:ℕ) (schedule center r K q t):=by
    simp only [schedule,ite_eq_left hin]
  rw [hnew]
  apply ite_eq_right
  intro hh
  exact (first_none_iff _ _ _ _ _ _).mp hh t
    (inserted_covers center _ hr hK t (schedule_before _ _ _ _ _) life rad p hp)

end KServer.TierEdits

end


/-! The literal chronological tier edits inside a complete level, including
heavy-priority shadowing. Noncoverage deliberately ignores earlier structures. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelTierEdits
open LevelKeys LevelCoverage LevelLaw FiniteExperiment TierProcess Pilot
open ActualRoster Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : ℝ :=
  indicator (PriorityKeys.key (PriorityKeys.stageBefore (keys s law hr σ a t)
    (keys s law hr σ a (t+1)) (i:Structure k)) p ≠
    PriorityKeys.key (PriorityKeys.stageAfter (keys s law hr σ a t)
    (keys s law hr σ a (t+1)) (i:Structure k)) p)

def uncovered (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : ℝ :=
  indicator (keys s law hr σ a t (i:Structure k) p=none)

def inserted (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (t:ℕ) (i:Tier k) : Prop :=
  insertTest (request s σ) (schedule (request s σ) r (tierK (height i))
    (tierQualifies s law r σ i) t) r (tierK (height i)) t (tierQualifies s law r σ i t)

def retirement (s:Configuration k Y) (law:RequestLaw Y H) (r:ℝ)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : Prop :=
  retired (request s σ) (schedule (request s σ) r (tierK (height i))
    (tierQualifies s law r σ i) t) (schedule (request s σ) r (tierK (height i))
    (tierQualifies s law r σ i) (t+1)) r (a.2 i).1 (a.2 i).2 p

lemma charge_nonneg (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) : 0 ≤ charge s law hr σ a t i p :=
  indicator_nonneg _

lemma charge_le (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y) :
    charge s law hr σ a t i p ≤ indicator (keys s law hr σ a t (i:Structure k) p≠
      keys s law hr σ a (t+1) (i:Structure k) p) :=
  PriorityKeys.stage_charge _ _ _ _

lemma stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i) :
    charge s law hr σ a t i p+uncovered s law hr σ a (t+1) i p-
      uncovered s law hr σ a t i p ≤ 2*indicator (retirement s law r σ a t i p) := by
  have ht:=TierEdits.stationary (request s σ) hr (tierQualifies s law r σ i)
    (a.2 i).1 (a.2 i).2 t p hin
  have hc:=charge_le s law hr σ a t i p
  dsimp only [uncovered,retirement,keys] at hc ⊢
  linarith

lemma mover (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i) :
    charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i (σ t)-
      uncovered s law hr.le σ a t i p ≤ indicator (retirement s law r σ a t i p) := by
  have ht:=TierEdits.mover (request s σ) hr
    (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i)
    (a.2 i).1 (a.2 i).2 t p hin
  rw [request_fin] at ht
  have hc:=charge_le s law hr.le σ a t i p
  dsimp only [uncovered,retirement,keys] at hc ⊢
  linarith

lemma no_insert_charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y)
    (hin:¬inserted s law r σ t i) : charge s law hr σ a t i p=0 := by
  apply le_antisymm _ (charge_nonneg s law hr σ a t i p)
  have hc:=charge_le s law hr σ a t i p
  have he:=congrFun (TierEdits.no_insert (request s σ) hr
    (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t hin) p
  change keys s law hr σ a (t+1) (i:Structure k) p=keys s law hr σ a t (i:Structure k) p at he
  simpa only [he,ne_self_iff_false,indicator,ite_false] using hc

lemma no_insert_stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:ℕ) (i:Tier k) (p:Y)
    (hin:¬inserted s law r σ t i) :
    charge s law hr σ a t i p+uncovered s law hr σ a (t+1) i p-
      uncovered s law hr σ a t i p=0 := by
  rw [no_insert_charge s law hr σ a t i p hin,zero_add]
  have he:=congrFun (TierEdits.no_insert (request s σ) hr
    (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t hin) p
  change keys s law hr σ a (t+1) (i:Structure k) p=keys s law hr σ a t (i:Structure k) p at he
  change indicator (_=none)-indicator (_=none)=0
  rw [he,sub_self]

lemma covered_qualified (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k)
    (hq:tierQualifies s law r σ i t) : uncovered s law hr.le σ a (t.val+1) i (σ t)=0 := by
  obtain ⟨b,hb⟩:=TierKeys.guaranteed_coverage (request s σ) hr
    (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i)
    t t.isLt hq (a.2 i).1 (a.2 i).2
  rw [request_fin] at hb
  change keys s law hr.le σ a (t.val+1) (i:Structure k) (σ t)=some b at hb
  change indicator (_=none)=0
  rw [hb]
  exact ite_eq_right (Option.some_ne_none _)

lemma no_insert_mover (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:¬inserted s law r σ t i) :
    charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i (σ t)-
      uncovered s law hr.le σ a t i p ≤
        if tierQualifies s law r σ i t then 0 else
          indicator (keys s law hr.le σ a (t.val+1) (i:Structure k) (σ t)≠
            keys s law hr.le σ a (t.val+1) (i:Structure k) p) := by
  rw [no_insert_charge s law hr.le σ a t i p hin,zero_add]
  by_cases hq:tierQualifies s law r σ i t
  · rw [ite_eq_left hq,covered_qualified s law hr σ a t i hq]
    exact sub_nonpos.mpr (indicator_nonneg _)
  · rw [ite_eq_right hq]
    have he:=congrFun (TierEdits.no_insert (request s σ) hr.le
      (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t hin) p
    change keys s law hr.le σ a (t.val+1) (i:Structure k) p=keys s law hr.le σ a t (i:Structure k) p at he
    unfold uncovered
    rw [←he]
    unfold indicator
    split_ifs with hx hp hn hp hn hn <;> try norm_num
    all_goals simp_all

lemma heavy_inner_covers (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (p:Y)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p ≤ heavyGamma*r) : ∃ b,keys s law hr.le σ a (t.val+1) (⊥:Structure k) p=some b := by
  obtain ⟨c,hc,hd⟩:=heavy_near_center s law σ t hr.le hh
  have hv:=HeavySchedule.run_valid s law hr heavyGamma heavyDelta σ a.1 (t.val+1)
  have hC:=HeavyCenters.centers_separated s law r heavyGamma heavyDelta σ (t.val+1)
  have hcp:dist c p ≤ (HeavySchedule.run s law r heavyGamma heavyDelta σ a.1 (t.val+1)).rad c:=by
    have hγ:heavyGamma ≤ 1:=by norm_num [heavyGamma]
    have hm:=mul_le_mul_of_nonneg_right hγ hr.le
    linarith [dist_triangle c (σ t) p,(hv.1 c hc).1]
  have he:=(HeavyKeys.centerKey_some hr hC (fun b hb=>(hv.1 b hb).2)).mpr ⟨hc,hcp⟩
  refine ⟨(HeavySchedule.run s law r heavyGamma heavyDelta σ a.1 (t.val+1)).label c,?_⟩
  change HeavyKeys.key _ _ _ _ _ _ _ _ _=some _
  simp only [HeavyKeys.key,he,Option.map_some]

lemma heavy_inner_charge (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p ≤ heavyGamma*r) : charge s law hr.le σ a t i p=0 := by
  obtain ⟨b,hb⟩:=heavy_inner_covers s law hr σ a t p hh hp
  have he:=PriorityKeys.stage_shadow (I:=Structure k) (keys s law hr.le σ a t)
    (keys s law hr.le σ a (t.val+1)) (j:=(i:Structure k)) (WithBot.bot_lt_coe i) p b hb
  exact ite_eq_right (not_not.mpr he)

lemma heavy_inner_stationary (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (hp:dist (σ t) p ≤ heavyGamma*r) :
    charge s law hr.le σ a t i p+uncovered s law hr.le σ a (t.val+1) i p-
      uncovered s law hr.le σ a t i p ≤ 0 := by
  rw [heavy_inner_charge s law hr σ a t i p hh hp,zero_add]
  have hcov:=TierEdits.covered_inner (request s σ) hr
    (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i)
    (a.2 i).1 (a.2 i).2 t hin p
    (by rw [request_fin]; exact hp.trans (mul_le_of_le_one_left hr.le (by norm_num [heavyGamma])))
  change uncovered s law hr.le σ a (t.val+1) i p=0 at hcov
  rw [hcov]
  exact sub_nonpos.mpr (indicator_nonneg _)

end KServer.LevelTierEdits

end


/-! Average actual tier retirements over the full finite partition tape, not
conditionally on surviving entries. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelRetirement
open LevelKeys LevelCoverage LevelLaw LevelTierEdits FiniteExperiment TierProcess Pilot
open ActualRoster Chronological FiniteTape PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ}

lemma tier_lifetime_bound {r:ℝ} (hr:0 < r) (i:Tier k)
    (E:(Fin H→Lifetime (tierK (height i)))→(Fin H→FiniteBallLaw.Outcome Y r)→Prop)
    (c:ℝ) (hc:∀ rad,probability (fun _ : Fin H=>lifetimeLaw (tierK (height i)))
      (fun life=>E life rad)≤c) :
    (∑ a:Tape Y k H r,if E (a.2 i).1 (a.2 i).2 then weight r a else 0)≤c := by
  have he:=tier_event (H:=H) hr i (fun b=>E b.1 b.2)
  have heq : (∑ a:Tape Y k H r,if E (a.2 i).1 (a.2 i).2 then weight r a else 0)=
      ∑ b:(Fin H→Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r),
        if E b.1 b.2 then tierWeight r i b else 0 := by
    refine Eq.trans ?_ (he.trans ?_) <;> apply sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  rw [heq]
  simp only [Fintype.sum_prod_type,tierWeight,pair]
  rw [sum_comm]
  calc (∑ rad,∑ life,if E life rad then lifetimeWeight i life*radiusWeight r i rad else 0)=
        ∑ rad,radiusWeight r i rad*(∑ life,if E life rad then lifetimeWeight i life else 0) := by
          apply sum_congr rfl
          intro rad _
          rw [mul_sum]
          apply sum_congr rfl
          intro life _
          split_ifs <;> ring
       _ ≤ ∑ rad,radiusWeight r i rad*c := by
          apply sum_le_sum
          intro rad _
          apply mul_le_mul_of_nonneg_left _ (radius_nonneg hr i rad)
          exact hc rad
       _ = c := by rw [←sum_mul,radius_sum hr i,one_mul]

variable [NeZero k]

lemma retirement_bound (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:ℕ) (i:Tier k) (p:Y) (hin:inserted s law r σ t i) :
    (∑ a:Tape Y k H r,if retirement s law r σ a t i p then weight r a else 0) ≤
      49/(tierK (height i):ℝ) := by
  have hnew:schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) (t+1)=
      insert t (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t):=by
    change insertTest _ _ _ _ _ _ at hin
    simp only [schedule,ite_eq_left hin]
  unfold retirement
  rw [hnew]
  refine tier_lifetime_bound hr i (fun life rad => retired (request s σ)
    (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t)
    (insert t (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t))
    r life rad p) _ ?_
  intro rad
  exact insertion_retirement (request s σ) _ hr (tierK_ge_two (height_ge i)) t rad p

lemma retirement_far (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (a:Tape Y k H r) (t:Fin H) (i:Tier k) (p:Y)
    (hin:inserted s law r σ t i) (hp:22*r < dist (σ t) p) :
    ¬retirement s law r σ a t i p := by
  intro he
  have hnew:schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) (t.val+1)=
      insert (t:ℕ) (schedule (request s σ) r (tierK (height i)) (tierQualifies s law r σ i) t):=by
    change insertTest _ _ _ _ _ _ at hin
    simp only [schedule,ite_eq_left hin]
  unfold retirement at he
  rw [hnew] at he
  have hn:=retired_near (request s σ) _ hr t (schedule_before _ _ _ _ _) (a.2 i).1 (a.2 i).2 p he
  rw [request_fin,dist_comm] at hn
  exact not_lt_of_ge hn hp

def mean (r:ℝ) (f:Tape Y k H r→ℝ) : ℝ := ∑ a,weight r a*f a

omit [NeZero k] in
lemma mean_mono {r:ℝ} (hr:0<r) {f g:Tape Y k H r→ℝ} (h:∀ a,f a≤g a) : mean r f ≤ mean r g :=
  sum_le_sum (fun a _=>mul_le_mul_of_nonneg_left (h a) (weight_nonneg hr a))

omit [NeZero k] in
lemma mean_const {r:ℝ} (hr:0<r) (c:ℝ) : mean (Y:=Y) (k:=k) (H:=H) r (fun _=>c)=c := by
  unfold mean
  rw [←sum_mul,weight_sum hr,one_mul]

omit [NeZero k] in
lemma mean_indicator (r:ℝ) (E:Tape Y k H r→Prop) :
    mean r (fun a=>indicator (E a))=∑ a,if E a then weight r a else 0 := by
  unfold mean
  apply sum_congr rfl
  intro a _
  by_cases h:E a
  · simp only [indicator,ite_eq_left h,mul_one]
  · simp only [indicator,ite_eq_right h,mul_zero]

omit [NeZero k] in
lemma mean_scale (r:ℝ) (c:ℝ) (f:Tape Y k H r→ℝ) :
    mean r (fun a=>c*f a)=c*mean r f := by
  unfold mean
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

lemma stationary_mean (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hin:inserted s law r σ t i) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i p-uncovered s law hr.le σ a t i p) ≤
        if dist (σ t) p≤22*r ∧ ¬(mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
          (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)) ∧
          dist (σ t) p≤heavyGamma*r) then 98/(tierK (height i):ℝ) else 0 := by
  by_cases hp:dist (σ t) p≤22*r
  · by_cases hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
          (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)) ∧
          dist (σ t) p≤heavyGamma*r
    · rw [ite_eq_right (fun h=>h.2 hh)]
      exact (mean_mono hr (fun a=>heavy_inner_stationary s law hr σ a t i p hin hh.1 hh.2)).trans_eq (mean_const hr 0)
    · rw [ite_eq_left ⟨hp,hh⟩]
      have hb:=mean_mono hr (fun a=>LevelTierEdits.stationary s law hr.le σ a t i p hin)
      rw [mean_scale,mean_indicator] at hb
      have hc:=mul_le_mul_of_nonneg_left (retirement_bound s law hr σ t i p hin) (by norm_num : (0:ℝ)≤2)
      exact hb.trans (by convert hc using 1; ring)
  · rw [ite_eq_right (fun h=>hp h.1)]
    have hb:=mean_mono hr (fun a=>LevelTierEdits.stationary s law hr.le σ a t i p hin)
    have hz (a:Tape Y k H r):indicator (retirement s law r σ a t i p)=0:=
      ite_eq_right (retirement_far s law hr σ a t i p hin (lt_of_not_ge hp))
    simp only [hz,mul_zero,mean_const hr] at hb
    exact hb

lemma mover_mean (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hin:inserted s law r σ t i) :
    mean r (fun a=>LevelTierEdits.charge s law hr.le σ a t i p+
      uncovered s law hr.le σ a (t.val+1) i (σ t)-uncovered s law hr.le σ a t i p) ≤
        49/(tierK (height i):ℝ) := by
  have hb:=mean_mono hr (fun a=>LevelTierEdits.mover s law hr σ a t i p hin)
  rw [mean_indicator] at hb
  exact hb.trans (retirement_bound s law hr σ t i p hin)

end KServer.LevelRetirement

end


/-! Exact scale-log sums for the true post-request metric posterior. The same
absolute shift works for the heavy test and all dyadic tier tests. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelScale
open FiniteExperiment Pilot LevelCoverage TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type*} [Fintype Y] [MetricSpace Y]

lemma log_ball_bounds (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {k r:ℝ} (hk:∑ y,μ y=k) (hr:0 ≤ r) :
    Real.log (mass μ (ball x r)) ∈ Set.Icc 0 (Real.log k) := by
  have hl:1 ≤ mass μ (ball x r):=hx.trans (single_le_sum (fun y _=>hμ y)
    (by simp only [ball,mem_filter,mem_univ,true_and,dist_self]; exact hr))
  have hu:mass μ (ball x r) ≤ k:=by simpa only [hk] using ball_mass_total μ hμ x r
  exact ⟨Real.log_nonneg hl,Real.log_le_log (by linarith) hu⟩

lemma mass_positive (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {r:ℝ} (hr:0 ≤ r) : 0 < mass μ (ball x r) := by
  have hl:1 ≤ mass μ (ball x r):=hx.trans (single_le_sum (fun y _=>hμ y)
    (by simp only [ball,mem_filter,mem_univ,true_and,dist_self]; exact hr))
  linarith

lemma logratio_sum (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {k r₀ τ γ D:ℝ} (hk:∑ y,μ y=k) (hr:0 ≤ r₀) (hτ:0 ≤ τ)
    (hγ:0 < γ) (hγD:γ ≤ D) (p n:ℕ) (hp:D ≤ γ*τ^p) :
    (∑ j∈range n,Real.log (mass μ (ball x (D*radius r₀ τ j))/
      mass μ (ball x (γ*radius r₀ τ j)))) ≤ p*Real.log k := by
  have hrad (j:ℕ):0 ≤ radius r₀ τ j:=mul_nonneg hr (pow_nonneg hτ _)
  have hm (j:ℕ):0 < mass μ (ball x (γ*radius r₀ τ j)):=
    mass_positive μ hμ x hx (mul_nonneg hγ.le (hrad j))
  have hM (j:ℕ):0 < mass μ (ball x (D*radius r₀ τ j)):=
    mass_positive μ hμ x hx (mul_nonneg (hγ.le.trans hγD) (hrad j))
  have hstep (j:ℕ):mass μ (ball x (D*radius r₀ τ j)) ≤
      mass μ (ball x (γ*radius r₀ τ (j+p))):=by
    apply ball_mass_mono μ hμ x
    rw [radius_add]
    nlinarith [mul_le_mul_of_nonneg_right hp (hrad j)]
  calc _ ≤ ∑ j∈range n,(Real.log (mass μ (ball x (γ*radius r₀ τ (j+p))))-
          Real.log (mass μ (ball x (γ*radius r₀ τ j)))) := by
        apply sum_le_sum
        intro j _
        rw [Real.log_div (hM j).ne' (hm j).ne']
        exact sub_le_sub_right (Real.log_le_log (hM j) (hstep j)) _
       _ ≤ _ := by
        simpa using ScaleMass.shifted_sum_le (fun j=>Real.log (mass μ (ball x (γ*radius r₀ τ j))))
          0 (Real.log k) (fun j=>log_ball_bounds μ hμ x hx hk (mul_nonneg hγ.le (hrad j))) n p

lemma nonheavy_count (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (hx:1 ≤ μ x)
    {k r₀ τ γ D δ:ℝ} (hk:∑ y,μ y=k) (hr:0 ≤ r₀) (hτ:0 ≤ τ)
    (hγ:0 < γ) (hγD:γ ≤ D) (hδ:0 < δ) (p n:ℕ) (hp:D ≤ γ*τ^p) :
    (∑ j∈range n,if mass μ (ball x (D*radius r₀ τ j)) ≤
      (1+δ)*mass μ (ball x (γ*radius r₀ τ j)) then (0:ℝ) else 1)
      ≤ (p*Real.log k)/Real.log (1+δ) := by
  have hlog:0 < Real.log (1+δ):=Real.log_pos (by linarith)
  apply (le_div_iff₀ hlog).mpr
  trans ∑ j∈range n,Real.log (mass μ (ball x (D*radius r₀ τ j))/
      mass μ (ball x (γ*radius r₀ τ j)))
  · rw [sum_mul]
    apply sum_le_sum
    intro j _
    have hrad:0 ≤ radius r₀ τ j:=mul_nonneg hr (pow_nonneg hτ _)
    have hm:=mass_positive μ hμ x hx (mul_nonneg hγ.le hrad)
    have hM:=mass_positive μ hμ x hx (mul_nonneg (hγ.le.trans hγD) hrad)
    have hab:=ball_mass_mono μ hμ x (mul_le_mul_of_nonneg_right hγD hrad)
    split_ifs with hh
    · rw [zero_mul]
      exact Real.log_nonneg ((le_div_iff₀ hm).mpr (by simpa using hab))
    · rw [one_mul]
      apply Real.log_le_log (by linarith : 0 < 1+δ)
      exact (le_div_iff₀ hm).mpr (le_of_lt (lt_of_not_ge hh))
  · exact logratio_sum μ hμ x hx hk hr hτ hγ hγD p n hp

lemma tier_shift {τ:ℝ} (hτ:2 ≤ τ) : 100*tierTemplate.R ≤ tierGamma*τ^60 := by
  have hp:(2:ℝ)^60 ≤ τ^60:=pow_le_pow_left₀ (by norm_num) hτ _
  have hc:100*tierTemplate.R ≤ tierGamma*(2:ℝ)^60:=by norm_num [tierTemplate,tierGamma]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num [tierGamma]))

lemma heavy_shift {τ:ℝ} (hτ:2 ≤ τ) : (51200:ℝ) ≤ heavyGamma*τ^60 := by
  have hp:(2:ℝ)^60 ≤ τ^60:=pow_le_pow_left₀ (by norm_num) hτ _
  have hc:(51200:ℝ) ≤ heavyGamma*(2:ℝ)^60:=by norm_num [heavyGamma]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num [heavyGamma]))

variable {k H:ℕ} [NeZero k]

lemma actual_logratio_sum (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) {r₀ τ:ℝ} (hr:0 ≤ r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n, logratio s law σ t (radius r₀ τ j)) ≤ 60*Real.log k := by
  exact logratio_sum (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (mu_served s law t σ hσ) (mu_total s law (t.val+1) σ hσ) hr (by linarith)
    (by norm_num [tierGamma]) (by norm_num [tierGamma,tierTemplate]) 60 n (tier_shift hτ)

lemma actual_nonheavy_count (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) {r₀ τ:ℝ} (hr:0 ≤ r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n,if mass (mu s law (t.val+1) σ) (ball (σ t) (51200*radius r₀ τ j)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (ball (σ t) (heavyGamma*radius r₀ τ j)) then (0:ℝ) else 1)
      ≤ (60*Real.log k)/Real.log (1+heavyDelta) := by
  exact nonheavy_count (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (mu_served s law t σ hσ) (mu_total s law (t.val+1) σ hσ) hr (by linarith)
    (by norm_num [heavyGamma]) (by norm_num [heavyGamma]) (by norm_num [heavyDelta])
    60 n (heavy_shift hτ)
end KServer.LevelScale

end


/-! The complete-level first-covering probability bound, with its individual
local log ratio (not the largest tier times the number of scales). -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelSpatial
open LevelKeys LevelCoverage LevelLaw FiniteExperiment TierProcess Pilot
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _

lemma fin_prefix_sum (f:ℕ→ℝ) {N n:ℕ} (hn:n < N) :
    (∑ i:Fin N,if i.val ≤ n then f i else 0)=∑ i∈range (n+1),f i := by
  have he:=Fin.sum_univ_eq_sum_range (fun m:ℕ=>if m ≤ n then f m else 0) N
  rw [he]
  calc (∑ i∈range N,if i ≤ n then f i else 0)=∑ i∈range (n+1),if i ≤ n then f i else 0 := by
        symm
        refine sum_subset (range_mono (by omega)) ?_
        intro i hi hni
        exact ite_eq_right (by simp only [mem_range] at hni; omega)
       _ = _ := by apply sum_congr rfl; intro i hi; exact ite_eq_left (by have := mem_range.mp hi; omega)

lemma structure_prefix_sum {k:ℕ} (p:Structure k→ℝ) (i:Tier k) :
    (∑ j∈univ.filter (fun j:Structure k=>j ≤ (i:Structure k)),p j)=
      p (⊥:Structure k)+∑ j:Tier k,if j ≤ i then p (j:Structure k) else 0 := by
  let f : Structure k → ℝ := fun j=>if j ≤ (i:Structure k) then p j else 0
  have hs : (∑ j∈univ.filter (fun j:Structure k=>j ≤ (i:Structure k)),p j)=∑ j:Structure k,f j := by
    rw [sum_filter]
  rw [hs]
  let e : Structure k ≃ Option (Tier k) := Equiv.refl _
  rw [Fintype.sum_equiv e f (fun j=>f (e.symm j)) (fun _=>rfl)]
  have he:=Fintype.sum_option (fun j:Option (Tier k)=>f (e.symm j))
  rw [he]
  have hb : f (e.symm none)=p (⊥:Structure k) := by
    change f (⊥:Structure k)=_
    simp only [f,bot_le,ite_true]
  rw [hb]
  congr 1
  apply sum_congr rfl
  intro j _
  change (if (j:Structure k) ≤ (i:Structure k) then p (j:Structure k) else 0)=_
  simp only [WithBot.coe_le_coe]

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

def separation (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (t:ℕ) (x y:Y) : ℝ :=
  ∑ a:Tape Y k H r,if map s law hr σ a t x≠map s law hr σ a t y then weight r a else 0

lemma separation_nonneg (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) : 0 ≤ separation s law hr.le σ t x y :=
  sum_nonneg (fun a _=>by split_ifs <;> first | exact weight_nonneg hr a | exact le_rfl)

lemma separation_le_one (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) : separation s law hr.le σ t x y ≤ 1 := by
  calc _ ≤ ∑ a:Tape Y k H r,weight r a := by
        apply sum_le_sum; intro a _; split_ifs <;> first | exact le_rfl | exact weight_nonneg hr a
       _ = 1 := weight_sum hr

lemma separation_self (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (t:ℕ) (x:Y) : separation s law hr σ t x x=0 := by
  simp [separation]

lemma prefix_bound (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) (hxy:4*dist x y < r)
    (i:Tier k) (hi:∀ a:Tape Y k H r,keys s law hr.le σ a t (some i) x≠none) :
    separation s law hr.le σ t x y ≤ dist x y/(4*r)+
      (262*dist x y/r)*(∑ j∈range (i.val+1),(2:ℝ)^j) := by
  have hp:=PriorityKeys.probability_prefix_bound (I:=Structure k) (weight r) (weight_nonneg hr)
    (fun a:Tape Y k H r=>keys s law hr.le σ a t) x y (i:Structure k) hi
  have he : separation s law hr.le σ t x y =
      ∑ a:Tape Y k H r,if PriorityKeys.key (I:=Structure k) (keys s law hr.le σ a t) x ≠
        PriorityKeys.key (I:=Structure k) (keys s law hr.le σ a t) y then weight r a else 0 := by
    apply sum_congr rfl
    intro a _
    unfold LevelKeys.map
    split_ifs <;> rfl
  have hp' : separation s law hr.le σ t x y ≤
      ∑ j∈univ.filter (fun j:Structure k=>j ≤ (i:Structure k)),
        ∑ a:Tape Y k H r,if keys s law hr.le σ a t j x≠keys s law hr.le σ a t j y then weight r a else 0 := by
    rw [he]
    convert hp using 1
    · apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
    · simp only [sum_filter]
      apply sum_congr rfl
      intro j _
      split_ifs <;> rfl
  rw [structure_prefix_sum] at hp'
  refine hp'.trans ?_
  apply add_le_add (heavy_spatial s law hr σ t x y hxy)
  have hs:(∑ j:Tier k,if j ≤ i then height j else 0)=∑ j∈range (i.val+1),(2:ℝ)^j := by
    exact fin_prefix_sum (fun n=>(2:ℝ)^n) i.isLt
  rw [←hs,mul_sum]
  apply sum_le_sum
  intro j _
  by_cases hj:j ≤ i
  · simp only [hj,ite_true]
    have hd:dist x y ≤ r:=by linarith [dist_nonneg (x:=x) (y:=y)]
    have hb:=tier_spatial s law hr σ t j x y hd
    have hl:Real.log (1+(tierK (height j):ℝ)^2) ≤ 131*height j:=
      TierDyadic.radius_coefficient (height_ge j)
    apply hb.trans
    have hc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ) ≤ 2))
      (div_nonneg (dist_nonneg (x:=x) (y:=y)) hr.le)
    convert hc using 1 <;> ring
  · simp only [hj,ite_false,mul_zero,le_refl]

lemma request_bound (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) (y:Y)
    (hxy:4*dist (σ t) y < r) :
    separation s law hr.le σ (t.val+1) (σ t) y ≤
      1050*(1+logratio s law σ t r)*dist (σ t) y/r := by
  let i:Tier k:=⟨firstTier s law σ t r,by have hh:=firstTier_le s law σ hσ t hr.le; omega⟩
  have hq:tierQualifies s law r σ i t:=firstTier_qualifies s law σ hσ t hr.le
  have hi (a:Tape Y k H r):keys s law hr.le σ a (t.val+1) (some i) (σ t)≠none:=by
    obtain ⟨b,hb⟩:=TierKeys.guaranteed_coverage (request s σ) hr
      (lt_of_lt_of_le (by omega : 0 < 2) (tierK_ge_two (height_ge i)))
      (tierQualifies s law r σ i) t t.isLt hq (a.2 i).1 (a.2 i).2
    change TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
      (a.2 i).1 (a.2 i).2 (t.val+1) (σ t)≠none
    rw [request_fin] at hb
    rw [hb]
    exact Option.some_ne_none _
  have hb:=prefix_bound s law hr σ (t.val+1) (σ t) y hxy i hi
  have hL:=logratio_bounds s law σ hσ t hr.le
  have hsum: (∑ j∈range (i.val+1),(2:ℝ)^j) ≤ 4*(1+logratio s law σ t r):=
    TierDyadic.qualified_sum hL.1
  have hmul:=mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 262*dist (σ t) y/r)
  have hc:dist (σ t) y/(4*r) ≤ 2*(1+logratio s law σ t r)*dist (σ t) y/r:=by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*r) hr).mpr
    have hd:=mul_nonneg hL.1 (dist_nonneg (x:=σ t) (y:=y))
    have hdr:=mul_nonneg hd hr.le
    nlinarith [mul_nonneg (dist_nonneg (x:=σ t) (y:=y)) hr.le]
  calc _ ≤ dist (σ t) y/(4*r)+(262*dist (σ t) y/r)*(∑ j∈range (i.val+1),(2:ℝ)^j) := hb
       _ ≤ 2*(1+logratio s law σ t r)*dist (σ t) y/r+(262*dist (σ t) y/r)*(4*(1+logratio s law σ t r)) := add_le_add hc hmul
       _ = _ := by ring

lemma map_eq_of_heavy (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:Fin H) (y:Y) (hxy:4*dist (σ t) y < r)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r)))
    (a:Tape Y k H r) : map s law hr.le σ a (t.val+1) (σ t)=map s law hr.le σ a (t.val+1) y := by
  obtain ⟨b,hb,hby⟩:=heavy_agrees s law σ t hr hh a.1 y hxy
  by_contra hn
  obtain ⟨j,hj,hd⟩:=PriorityKeys.key_ne_prefix (keys s law hr.le σ a (t.val+1)) (σ t) y none
    (by change HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 (t.val+1) (σ t)≠none
        rw [hb]; exact Option.some_ne_none _) hn
  have he:j=none:=bot_unique hj
  subst j
  exact hd (hb.trans hby.symm)

lemma heavy_zero (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:Fin H) (y:Y) (hxy:4*dist (σ t) y < r)
    (hh:mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*r)) ≤
      (1+heavyDelta)*mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*r))) :
    separation s law hr.le σ (t.val+1) (σ t) y=0 := by
  apply sum_eq_zero
  intro a _
  exact ite_eq_right (not_not.mpr (map_eq_of_heavy s law hr σ t y hxy hh a))

/-- The complete-level estimate (final-map-separation), with an explicit
absolute factor and no number-of-scales or largest-tier multiplier. -/
lemma spatial_sum (s:Configuration k Y) (law:RequestLaw Y H)
    (σ:Fin H→Y) (hσ:0 < law.val σ) (t:Fin H) (y:Y)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n, Pilot.radius r₀ τ j *
      separation s law (Pilot.radius_pos hr (by linarith) j).le σ (t.val+1) (σ t) y) ≤
      (8+1050*(60/Real.log (1+heavyDelta)+60)*Real.log k)*dist (σ t) y := by
  let R:=Pilot.radius r₀ τ
  let L (j:ℕ):=logratio s law σ t (R j)
  let N (j:ℕ):ℝ:=if Pilot.mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (51200*R j)) ≤
    (1+heavyDelta)*Pilot.mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (heavyGamma*R j)) then 0 else 1
  have hR (j:ℕ):0 < R j:=Pilot.radius_pos hr (by linarith) j
  have hL (j:ℕ):0 ≤ L j:=(logratio_bounds s law σ hσ t (hR j).le).1
  have hN (j:ℕ):0 ≤ N j:=by dsimp [N]; split_ifs <;> norm_num
  have hpoint (j:ℕ):R j*separation s law (hR j).le σ (t.val+1) (σ t) y ≤
      (if R j ≤ 4*dist (σ t) y then R j else 0)+1050*dist (σ t) y*(N j+L j):=by
    by_cases hsmall:R j ≤ 4*dist (σ t) y
    · rw [ite_eq_left hsmall]
      have hs:=mul_le_mul_of_nonneg_left (separation_le_one s law (hR j) σ (t.val+1) (σ t) y) (hR j).le
      have hmore:0 ≤ 1050*dist (σ t) y*(N j+L j):=mul_nonneg (by positivity) (add_nonneg (hN j) (hL j))
      linarith
    · rw [ite_eq_right hsmall]
      have hbig:4*dist (σ t) y < R j:=lt_of_not_ge hsmall
      dsimp only [N]
      split_ifs with hh
      · rw [heavy_zero s law (hR j) σ t y hbig hh,mul_zero,zero_add,zero_add]
        exact mul_nonneg (by positivity) (hL j)
      · have hs:=request_bound s law (hR j) σ hσ t y hbig
        have hm:=mul_le_mul_of_nonneg_left hs (hR j).le
        have he:R j*(1050*(1+L j)*dist (σ t) y/R j)=1050*dist (σ t) y*(1+L j):=by field_simp [(hR j).ne']
        change R j*separation s law (hR j).le σ (t.val+1) (σ t) y ≤ R j*(1050*(1+L j)*dist (σ t) y/R j) at hm
        simpa only [he,zero_add] using hm
  have hsum:=sum_le_sum (fun j (_:j∈range n)=>hpoint j)
  rw [sum_add_distrib,←mul_sum,sum_add_distrib] at hsum
  have hsmall:=Pilot.radius_truncated_sum hr.le hτ (by positivity : 0 ≤ 4*dist (σ t) y) n
  have hlogs:=LevelScale.actual_logratio_sum s law σ hσ t hr.le hτ n
  have hcount:=LevelScale.actual_nonheavy_count s law σ hσ t hr.le hτ n
  have hlarge:=mul_le_mul_of_nonneg_left (add_le_add hcount hlogs)
    (by positivity : 0 ≤ 1050*dist (σ t) y)
  have htotal:=hsum.trans (add_le_add hsmall hlarge)
  convert htotal using 1; first | rfl | ring
end KServer.LevelSpatial

end


/-! Physical movement of the tier noncoverage potential on steps without an
insertion.  Unqualified dyadic heights sum against the local log ratio. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelNoInsert
open ActualRoster LevelKeys LevelCoverage LevelLaw LevelTierEdits LevelRetirement FiniteExperiment TierProcess Pilot
attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _

lemma filtered_powers {L:ℝ} (hL:0 ≤ L) (n:ℕ) :
    (∑ i∈range n,if (2:ℝ)^i<L then (2:ℝ)^i else 0) ≤ 2*L := by
  induction n with
  | zero => simp only [range_zero,sum_empty]; linarith
  | succ n ih =>
    by_cases hn:(2:ℝ)^n<L
    · have he : (∑ i∈range (n+1),if (2:ℝ)^i<L then (2:ℝ)^i else 0)=
          ∑ i∈range (n+1),(2:ℝ)^i := by
        apply sum_congr rfl
        intro i hi
        exact ite_eq_left ((pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
          (by have hh:=mem_range.mp hi; omega)).trans_lt hn)
      rw [he,TierDyadic.tier_sum]
      linarith
    · rw [sum_range_succ,ite_eq_right hn,add_zero]
      exact ih

lemma tier_count (k:ℕ) : (Fintype.card (Tier k):ℝ) ≤ 4*(1+Real.log k) := by
  by_cases hk:k=0
  · subst k
    norm_num [Tier,TierDyadic.index_zero (show (0:ℝ) ≤ 1 by norm_num)]
  have hl:0 ≤ Real.log k:=Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
  have hp:=TierDyadic.qualified_sum hl
  have hi : (Fintype.card (Tier k):ℝ) ≤ ∑ i∈range (TierDyadic.index (Real.log k)+1),(2:ℝ)^i := by
    calc _ = ∑ i∈range (TierDyadic.index (Real.log k)+1),(1:ℝ) := by simp [Tier]
         _ ≤ _ := sum_le_sum (fun i _=>one_le_pow₀ (by norm_num))
  exact hi.trans hp

variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ} [NeZero k]

lemma unqualified_height_sum (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) :
    (∑ i:Tier k,if tierQualifies s law r σ i t then 0 else height i) ≤
      2*logratio s law σ t r := by
  trans ∑ i:Tier k,if height i<logratio s law σ t r then height i else 0
  · apply sum_le_sum
    intro i _
    by_cases hq:tierQualifies s law r σ i t
    · rw [ite_eq_left hq]; split_ifs
      · exact (show (0:ℝ) ≤ 1 by norm_num).trans (height_ge i)
      · rfl
    · have hi:height i<logratio s law σ t r:=lt_of_not_ge (fun hn=>hq (qualifies_of_log s law σ hs t hr hn))
      rw [ite_eq_right hq,ite_eq_left hi]
  · unfold height
    have he:=Fin.sum_univ_eq_sum_range (fun j:ℕ=>if (2:ℝ)^j<logratio s law σ t r then (2:ℝ)^j else 0) (TierDyadic.index (Real.log k)+1)
    rw [he]
    exact filtered_powers (logratio_bounds s law σ hs t hr).1 _

/-- Positive error is zero on insertion steps here; those steps are separately
charged to the actual retirement and pilot budgets. -/
def error (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 ≤ r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) : ℝ :=
  if inserted s law r σ t i then 0 else mean r (fun a=>
    LevelTierEdits.charge s law hr σ a t i p+uncovered s law hr σ a (t.val+1) i (σ t)-
      uncovered s law hr σ a t i p)

lemma error_le_one (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) : error s law hr.le σ t i p ≤ 1 := by
  unfold error
  split_ifs with hin
  · norm_num
  · have hb:=mean_mono hr (fun a=>no_insert_mover s law hr σ a t i p hin)
    refine hb.trans ((mean_mono hr (fun a=>?_)).trans_eq (mean_const hr 1))
    split_ifs
    · norm_num
    · unfold indicator; split_ifs <;> norm_num

lemma error_spatial (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (t:Fin H) (i:Tier k) (p:Y) (hp:dist (σ t) p ≤ r) :
    error s law hr.le σ t i p ≤
      (262*dist (σ t) p/r)*(if tierQualifies s law r σ i t then 0 else height i) := by
  have hnon:0 ≤ 262*dist (σ t) p/r:=by positivity
  unfold error
  by_cases hin:inserted s law r σ t i
  · rw [ite_eq_left hin]
    exact mul_nonneg hnon (by split_ifs <;> first | rfl | exact (height_ge i).trans' (by norm_num))
  · rw [ite_eq_right hin]
    have hb:=mean_mono hr (fun a=>no_insert_mover s law hr σ a t i p hin)
    by_cases hq:tierQualifies s law r σ i t
    · simp only [ite_eq_left hq,mul_zero,mean_const hr] at hb ⊢
      exact hb
    · simp only [ite_eq_right hq] at hb ⊢
      rw [mean_indicator] at hb
      have hc:=LevelLaw.tier_spatial s law hr σ (t.val+1) i (σ t) p hp
      have hh:=mul_le_mul_of_nonneg_right (TierDyadic.radius_coefficient (height_ge i))
        (div_nonneg (dist_nonneg (x:=σ t) (y:=p)) hr.le)
      dsimp only [keys] at hb hc
      have hbound : (∑ a:Tape Y k H r,if TierKeys.key (request s σ) hr.le (tierK (height i))
          (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 (t.val+1) (σ t) ≠
          TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
            (a.2 i).1 (a.2 i).2 (t.val+1) p then weight r a else 0) ≤
          (262*dist (σ t) p/r)*height i := by
        refine hc.trans ?_
        convert mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
      apply hb.trans
      convert hbound using 1; first | rfl | (apply sum_congr rfl; intro a _; congr 1)

lemma level_error (s:Configuration k Y) (law:RequestLaw Y H) {r:ℝ} (hr:0 < r)
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) (p:Y) :
    r*(∑ i:Tier k,error s law hr.le σ t i p) ≤
      (if r ≤ 4*dist (σ t) p then (Fintype.card (Tier k):ℝ)*r else 0)+
        524*dist (σ t) p*logratio s law σ t r := by
  by_cases hp:r ≤ 4*dist (σ t) p
  · rw [ite_eq_left hp]
    have hb:=sum_le_sum (fun i (_:i∈univ)=>error_le_one s law hr σ t i p)
    simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at hb
    have hc:=mul_le_mul_of_nonneg_left hb hr.le
    have hn:=mul_nonneg (by positivity : 0 ≤ 524*dist (σ t) p) (logratio_bounds s law σ hs t hr.le).1
    nlinarith
  · rw [ite_eq_right hp,zero_add]
    have hdist:dist (σ t) p ≤ r:=by linarith [dist_nonneg (x:=σ t) (y:=p)]
    have hb:=sum_le_sum (fun i (_:i∈univ)=>error_spatial s law hr σ t i p hdist)
    rw [←mul_sum] at hb
    have hc:=hb.trans (mul_le_mul_of_nonneg_left (unqualified_height_sum s law hr.le σ hs t) (by positivity))
    have hd:=mul_le_mul_of_nonneg_left hc hr.le
    calc _ ≤ r*((262*dist (σ t) p/r)*(2*logratio s law σ t r)) := hd
         _ = _ := by field_simp [hr.ne']; ring

lemma scales_error (s:Configuration k Y) (law:RequestLaw Y H)
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) (p:Y)
    {r₀ τ:ℝ} (hr:0 < r₀) (hτ:2 ≤ τ) (n:ℕ) :
    (∑ j∈range n,Pilot.radius r₀ τ j *
      (∑ i:Tier k,error s law (Pilot.radius_pos hr (by linarith) j).le σ t i p)) ≤
      (32*(1+Real.log k)+31440*Real.log k)*dist (σ t) p := by
  have hb:=sum_le_sum (fun j (_:j∈range n)=>level_error s law (Pilot.radius_pos hr (by linarith) j) σ hs t p)
  rw [sum_add_distrib,←mul_sum] at hb
  have he:(∑ j∈range n,if Pilot.radius r₀ τ j ≤ 4*dist (σ t) p then
      (Fintype.card (Tier k):ℝ)*Pilot.radius r₀ τ j else 0)=
      (Fintype.card (Tier k):ℝ)*∑ j∈range n,if Pilot.radius r₀ τ j ≤ 4*dist (σ t) p then Pilot.radius r₀ τ j else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [he] at hb
  have hsmall:=mul_le_mul_of_nonneg_left (Pilot.radius_truncated_sum hr.le hτ
    (by positivity : 0 ≤ 4*dist (σ t) p) n) (Nat.cast_nonneg (Fintype.card (Tier k)): (0:ℝ) ≤ _)
  have hlarge:=mul_le_mul_of_nonneg_left (LevelScale.actual_logratio_sum s law σ hs t hr.le hτ n)
    (by positivity : 0 ≤ 524*dist (σ t) p)
  have hcount:=mul_le_mul_of_nonneg_right (tier_count k) (by positivity : 0 ≤ 8*dist (σ t) p)
  have ht:=hb.trans (add_le_add hsmall hlarge)
  nlinarith
end KServer.LevelNoInsert

end

end OAI
