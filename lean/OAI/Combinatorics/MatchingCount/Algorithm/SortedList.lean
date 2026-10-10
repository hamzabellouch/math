import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.FiniteTrial

namespace OAI

namespace MatchingFPRAS.Amplification
open Finset

variable {k : ℕ}

def sortedList (x : Fin (2*k+1) → ℚ) : List ℚ :=
  (List.ofFn x).mergeSort (· ≤ ·)

lemma sortedList_length (x : Fin (2*k+1) → ℚ) : (sortedList x).length=2*k+1 := by
  simp [sortedList]

def sortedValue (x : Fin (2*k+1) → ℚ) (i : Fin (2*k+1)) : ℚ :=
  (sortedList x)[i.val]'(by rw [sortedList_length]; exact i.isLt)

def median (x : Fin (2*k+1) → ℚ) : ℚ := sortedValue x ⟨k,by omega⟩

lemma sortedValue_monotone (x : Fin (2*k+1) → ℚ) : Monotone (sortedValue x) := by
  intro i j hij
  exact ((List.ofFn x).sortedLE_mergeSort).getElem_le_getElem_of_le hij

lemma ofFn_sortedValue (x : Fin (2*k+1) → ℚ) : List.ofFn (sortedValue x)=sortedList x := by
  apply List.ext_getElem
  · simp [sortedList_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

lemma majority_sorted (f : Fin (2*k+1) → ℚ) (hf : Monotone f) (a b : ℚ)
    (h : k < (univ.filter fun i => a ≤ f i ∧ f i ≤ b).card) :
    a ≤ f ⟨k,by omega⟩ ∧ f ⟨k,by omega⟩ ≤ b := by
  let z : Fin (2*k+1) := ⟨k,by omega⟩
  constructor
  · by_contra hc
    have hc' : f z < a := lt_of_not_ge hc
    have hs : (univ.filter fun i => a ≤ f i ∧ f i ≤ b) ⊆ Ioi z := by
      intro i hi
      apply mem_Ioi.mpr
      by_contra hnot
      have hlow := (mem_filter.mp hi).2.1
      have hm := hf (le_of_not_gt hnot)
      exact (not_lt_of_ge (hlow.trans hm)) hc'
    have hh := card_le_card hs
    rw [Fin.card_Ioi] at hh
    dsimp [z] at hh
    omega
  · by_contra hc
    have hc' : b < f z := lt_of_not_ge hc
    have hs : (univ.filter fun i => a ≤ f i ∧ f i ≤ b) ⊆ Iio z := by
      intro i hi
      apply mem_Iio.mpr
      by_contra hnot
      have hupp := (mem_filter.mp hi).2.2
      have hm := hf (le_of_not_gt hnot)
      exact (not_lt_of_ge (hm.trans hupp)) hc'
    have hh := card_le_card hs
    rw [Fin.card_Iio] at hh
    dsimp [z] at hh
    omega

lemma good_count (x : Fin (2*k+1) → ℚ) (a b : ℚ) :
    (univ.filter fun i => a ≤ x i ∧ x i ≤ b).card=
      ((List.ofFn x).map (fun q => if a ≤ q ∧ q ≤ b then 1 else 0)).sum := by
  rw [List.map_ofFn,List.sum_ofFn]
  exact Finset.card_filter _ _

lemma sorted_good_count (x : Fin (2*k+1) → ℚ) (a b : ℚ) :
    (univ.filter fun i => a ≤ sortedValue x i ∧ sortedValue x i ≤ b).card=
      (univ.filter fun i => a ≤ x i ∧ x i ≤ b).card := by
  rw [good_count,good_count,ofFn_sortedValue]
  exact ((List.mergeSort_perm (List.ofFn x) (· ≤ ·)).map _).sum_eq

theorem median_majority (x : Fin (2*k+1) → ℚ) (a b : ℚ)
    (h : k < (univ.filter fun i => a ≤ x i ∧ x i ≤ b).card) :
    a ≤ median x ∧ median x ≤ b := by
  apply majority_sorted (sortedValue x) (sortedValue_monotone x) a b
  rwa [sorted_good_count]

open Finset MatchingFPRAS.Adaptive MatchingFPRAS.Transport
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
lemma product_bad (r : ℕ) (B : Ω → Prop) (x : Fin r → Ω) :
    (∏ i : Fin r, (if B (x i) then (10:ℝ) else 1)) =
      (10:ℝ)^(univ.filter fun i=>B (x i)).card := by
  rw [← prod_filter]
  simp

lemma product_moment (μ : Law Ω) (r : ℕ) (B : Ω → Prop) :
    ∑ x : Fin r → Ω,(μ.iid r) x * (∏ i,if B (x i) then (10:ℝ) else 1) =
      (1+9*μ.event B)^r := by
  have he : (∑ x : Ω, μ x*(if B x then (10:ℝ) else 1))=1+9*μ.event B := by
    calc
      _ = ∑ x : Ω, (μ x+9*(if B x then μ x else 0)) := by
        apply sum_congr rfl
        intro x _
        split_ifs <;> ring
      _ = _ := by rw [sum_add_distrib,←mul_sum,μ.total]; rfl
  change (∑ x : Fin r → Ω,(∏ i,μ (x i)) * ∏ i,if B (x i) then (10:ℝ) else 1) = _
  simp_rw [←prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (_ : Fin r) (x : Ω)=>μ x*(if B x then (10:ℝ) else 1))]
  simp only [he,prod_const,card_univ,Fintype.card_fin]

lemma majority_tail (μ : Law Ω) (B : Ω → Prop) (hB : μ.event B≤1/10) (k : ℕ) :
    (μ.iid (2*k+1)).event (fun x=>k<(univ.filter fun i=>B (x i)).card) ≤ (2:ℝ)⁻¹^k := by
  have hM : (10:ℝ)^(k+1) * (μ.iid (2*k+1)).event
      (fun x=>k<(univ.filter fun i=>B (x i)).card) ≤ (1+9*μ.event B)^(2*k+1) := by
    rw [←product_moment μ (2*k+1) B]
    unfold Law.event
    rw [mul_sum]
    apply sum_le_sum
    intro x _
    rw [product_bad]
    split_ifs with hx
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
        ((μ.iid (2*k+1)).nonneg x) |>.trans_eq (mul_comm _ _)
    · rw [mul_zero]
      exact mul_nonneg ((μ.iid (2*k+1)).nonneg x) (by positivity)
  have hn : 0≤1+9*μ.event B := by have := μ.event_nonneg B; linarith
  have hu : (1+9*μ.event B)^(2*k+1) ≤ (2:ℝ)^(2*k+1) :=
    pow_le_pow_left₀ hn (by linarith) _
  have hdiv : (μ.iid (2*k+1)).event (fun x=>k<(univ.filter fun i=>B (x i)).card) ≤ (2:ℝ)^(2*k+1)/10^(k+1) := (le_div_iff₀ (by positivity : (0:ℝ)<10^(k+1))).mpr (by rw [mul_comm]; exact hM.trans hu)
  apply hdiv.trans
  calc
    (2:ℝ)^(2*k+1)/10^(k+1) = (1/5:ℝ)*(4/10)^k := by
      rw [pow_add,pow_add,pow_mul]
      simp only [pow_one]
      rw [div_mul_eq_div_mul_one_div,div_pow]
      ring
    _ ≤ (1/2:ℝ)^k := by
      have hpow : (4/10:ℝ)^k ≤ (1/2:ℝ)^k := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      calc
        _ ≤ (1:ℝ)*(4/10)^k := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ _ := by simpa using hpow
    _ = _ := by norm_num

lemma median_failure (μ : Law Ω) (out : Ω → ℚ) (a b : ℚ)
    (h : μ.event (fun x=>¬(a≤out x ∧ out x≤b))≤1/10) (k : ℕ) :
    (μ.iid (2*k+1)).event (fun x=>¬(a ≤ median (fun i=>out (x i)) ∧ median (fun i=>out (x i))≤b))
      ≤ (2:ℝ)⁻¹^k := by
  apply (Law.event_mono _ (fun x hx=>?_)).trans (majority_tail μ (fun y=>¬(a≤out y ∧ out y≤b)) h k)
  by_contra hh
  have hb := not_lt.mp hh
  have hs := card_filter_add_card_filter_not (s:=univ) (p:=fun i : Fin (2*k+1)=>a≤out (x i) ∧ out (x i)≤b)
  simp only [card_univ,Fintype.card_fin] at hs
  apply hx
  apply median_majority (k:=k) (fun i=>out (x i)) a b
  have hc : (univ.filter fun i : Fin (2*k+1)=>¬(a≤out (x i) ∧ out (x i)≤b)).card ≤ k := by
    convert hb using 1
    congr 1
    ext i
    simp
  omega

omit [Fintype Ω] in
lemma median_nonneg {k : ℕ} (out : Fin (2*k+1) → ℚ) (h : ∀ i,0≤out i) : 0 ≤ median out := by
  unfold median sortedValue
  have hp := List.mergeSort_perm (List.ofFn out) (· ≤ ·)
  have hx : (sortedList out)[k]'(by rw [sortedList_length]; omega) ∈ List.ofFn out :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
  rw [←hi]
  exact h i

open Finset MatchingFPRAS.Adaptive
open scoped Classical

def halfRepetitions (δ : ℚ) : ℕ := 5*(Nat.clog 2 ⌈δ⁻¹⌉₊+1)
lemma repetitions_source (δ : ℚ) : 2*halfRepetitions δ+1=10*(Nat.clog 2 ⌈δ⁻¹⌉₊+1)+1 := by
  unfold halfRepetitions
  ring
lemma amplification_precision (δ : ℚ) (hδ : 0<δ) : (2:ℝ)⁻¹^(halfRepetitions δ)≤(δ:ℝ) := by
  let m := Nat.clog 2 ⌈δ⁻¹⌉₊
  have hc : (δ:ℝ)⁻¹≤(⌈δ⁻¹⌉₊:ℝ) := by
    exact_mod_cast Nat.le_ceil (δ⁻¹)
  have hp : (⌈δ⁻¹⌉₊:ℝ)≤(2:ℝ)^m := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) ⌈δ⁻¹⌉₊
  have hd : (0:ℝ)<δ := by exact_mod_cast hδ
  have hh : (2:ℝ)⁻¹^m≤(δ:ℝ) := by
    rw [inv_pow]
    apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
    nlinarith [hc.trans hp,inv_pos.mpr hd,mul_inv_cancel₀ hd.ne']
  apply (pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num) (show m≤halfRepetitions δ by dsimp [m,halfRepetitions]; omega)).trans hh

variable {Ω : Type*} [Fintype Ω]
lemma median_delta (μ : Law Ω) (out : Ω → ℚ) (a b : ℚ)
    (h : μ.event (fun x=>¬(a≤out x ∧ out x≤b))≤1/10) (δ : ℚ) (hδ : 0<δ) :
    (μ.iid (2*halfRepetitions δ+1)).event
      (fun x=>¬(a≤ median (fun i=>out (x i)) ∧ median (fun i=>out (x i))≤b)) ≤ (δ:ℝ) :=
  (median_failure μ out a b h _).trans (amplification_precision δ hδ)
end MatchingFPRAS.Amplification

namespace MatchingFPRAS.FiniteTrial
open Finset Adaptive Amplification
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def amplifiedOutput (p : Trial.Parameters G) (δ : ℚ)
    (x : Fin (2*halfRepetitions δ+1) → (layers p p.K le_rfl).Ω) : ℚ :=
  median (fun i=>output p (x i))
lemma amplifiedOutput_nonneg (p : Trial.Parameters G) (δ : ℚ)
    (x : Fin (2*halfRepetitions δ+1) → (layers p p.K le_rfl).Ω) : 0≤amplifiedOutput p δ x :=
  median_nonneg _ (fun i=>output_nonneg p (x i))
theorem actual_finite_amplified_failure (p : Trial.Parameters G) (hZ : 0<Z G)
    (δ : ℚ) (hδ : 0<δ) :
    ((layers p p.K le_rfl).law.iid (2*halfRepetitions δ+1)).event
      (fun x=>¬((1-p.epsilon)*(Z G:ℚ)≤amplifiedOutput p δ x ∧
        amplifiedOutput p δ x≤(1+p.epsilon)*(Z G:ℚ))) ≤ (δ:ℝ) := by
  apply median_delta
  · exact (actual_finite_trial_failure p hZ).trans (by norm_num)
  · exact hδ
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Counting
instance scheduleDecidable (n : ℕ) (epsilon : ℚ) (k : ℕ) : Decidable (scheduleAdmissible n epsilon k) :=
  inferInstanceAs (Decidable (1≤k ∧ (n:ℚ)^(n/2)/(1+1/(n:ℚ))^k≤epsilon/32))
lemma schedule_exists (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    ∃ k,scheduleAdmissible n e k := by
  obtain ⟨k,hk,_⟩:=counting_schedule_exists n hn e he he1
  exact ⟨k,hk⟩
def leastSchedule (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) : ℕ :=
  Nat.find (schedule_exists n hn e he he1)
lemma leastSchedule_spec (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    scheduleAdmissible n e (leastSchedule n hn e he he1) := Nat.find_spec _
lemma leastSchedule_le (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1)
    (k : ℕ) (hk : scheduleAdmissible n e k) : leastSchedule n hn e he he1≤k := Nat.find_min' _ hk
lemma leastSchedule_log_bound (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    (leastSchedule n hn e he he1:ℝ)≤1+2*n*((n/2:ℕ)*Real.log n+Real.log (32/(e:ℝ))) := by
  obtain ⟨k,hk,_,hb⟩:=counting_schedule_exists n hn e he he1
  exact le_trans (by exact_mod_cast leastSchedule_le n hn e he he1 k hk) hb
end MatchingFPRAS.Counting
namespace MatchingFPRAS.FiniteTrial
def parameters (G : GraphInput) (hn : 2≤G.n) (heven : Even G.n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    Trial.Parameters G where
  hn:=hn
  even:=heven
  K:=Counting.leastSchedule G.n hn e he he1
  epsilon:=e
  epsilon_pos:=he
  epsilon_lt_one:=he1
  schedule:=Counting.leastSchedule_spec G.n hn e he he1
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.BitArithmetic
open Finset

def FractionBound (B : ℕ) (x : ℝ) : Prop :=
  ∃ a b : ℕ,0<b ∧ a≤B ∧ b≤B ∧ x=(a:ℝ)/b
lemma FractionBound.mono {B C : ℕ} {x : ℝ} (h : FractionBound B x) (hBC : B≤C) : FractionBound C x := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := h
  exact ⟨a,b,hb,ha.trans hBC,hbb.trans hBC,rfl⟩
lemma FractionBound.zero {B : ℕ} (hB : 1≤B) : FractionBound B 0 :=
  ⟨0,1,by omega,by omega,hB,by simp⟩
lemma FractionBound.one {B : ℕ} (hB : 1≤B) : FractionBound B 1 :=
  ⟨1,1,by omega,hB,hB,by simp⟩
lemma FractionBound.nat (a : ℕ) : FractionBound (a+1) a :=
  ⟨a,1,by omega,by omega,by omega,by simp⟩
lemma FractionBound.mul {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y) :
    FractionBound (B*C) (x*y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  refine ⟨a*c,b*d,Nat.mul_pos hb hd,Nat.mul_le_mul ha hc,Nat.mul_le_mul hbb hdd,?_⟩
  push_cast
  ring
lemma FractionBound.div {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y)
    (hy0 : 0<y) : FractionBound (B*C) (x/y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  have hc0 : 0<c := by
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    have hcr := (lt_div_iff₀ hd0).mp hy0
    exact_mod_cast (by simpa using hcr : (0:ℝ)<c)
  refine ⟨a*d,b*c,Nat.mul_pos hb hc0,Nat.mul_le_mul ha hdd,Nat.mul_le_mul hbb hc,?_⟩
  push_cast
  field_simp
lemma FractionBound.add {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y) :
    FractionBound (2*B*C) (x+y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  refine ⟨a*d+c*b,b*d,Nat.mul_pos hb hd,?_,?_,?_⟩
  · have h₁ := Nat.mul_le_mul ha hdd
    have h₂ := Nat.mul_le_mul hc hbb
    nlinarith
  · have h₁ := Nat.mul_le_mul hbb hdd
    nlinarith
  · have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
    have hd0 : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
lemma FractionBound.sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈s,FractionBound B (f i)) : FractionBound B (s.sup' hs f) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup' hs f
  rw [he]
  exact h i hi
lemma FractionBound.max {B : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound B y) :
    FractionBound B (max x y) := by
  rcases le_total x y with h|h
  · simpa [max_eq_right h] using hy
  · simpa [max_eq_left h] using hx
lemma FractionBound.min {B : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound B y) :
    FractionBound B (min x y) := by
  rcases le_total x y with h|h
  · simpa [min_eq_left h] using hx
  · simpa [min_eq_right h] using hy
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma cooling_fraction (n : ℕ) (hn : 0<n) : cooling n=(n:ℝ)/(n+1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold cooling
  field_simp
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.edge_ratio (s : ScaleState G j) (a b : Fin G.n) :
    s.nextActivity a b/s.activity a b=1 ∨ s.nextActivity a b/s.activity a b=Trial.cooling G.n := by
  have hs₀ := (s.positive a).ne'
  have hs₁ := (s.positive b).ne'
  have hr := (raw_pos G j a b).ne'
  have he : s.nextActivity a b/s.activity a b=raw G (j+1) a b/raw G j a b := by
    unfold ScaleState.nextActivity ScaleState.activity
    field_simp
  rw [he]
  unfold raw GraphBridge.rawActivity
  split_ifs
  · left; simp
  · right
    rw [pow_succ]
    exact mul_div_cancel_left₀ _ (pow_pos (cooling_pos G.n) j).ne'
lemma ScaleState.bag_reweight (s : ScaleState G j) (e : BagEdge (sourceBags s.activity K)) :
    bagReweight s.activity s.nextActivity K e=1 ∨
      bagReweight s.activity s.nextActivity K e=Trial.cooling G.n := by
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · unfold logicalActivity edgeActivity
      split_ifs <;> exact s.edge_ratio _ _
    · exact Or.inl rfl
  · exact Or.inl rfl
lemma product_binary_power {E : Type*} (A : Finset E) (f : E → ℝ) (c : ℝ)
    (hf : ∀ e∈A,f e=1 ∨ f e=c) : ∃ a≤A.card,∏ e∈A,f e=c^a := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨0,by simp,by simp⟩
  | @insert e A he ih =>
    obtain ⟨a,ha,hea⟩ := ih (fun i hi=>hf i (mem_insert_of_mem hi))
    rcases hf e (mem_insert_self _ _) with h|h
    · refine ⟨a,by simpa [card_insert_of_notMem he] using (Nat.le_succ_of_le ha),?_⟩
      rw [prod_insert he,h,one_mul,hea]
    · refine ⟨a+1,by simpa [card_insert_of_notMem he] using Nat.succ_le_succ ha,?_⟩
      rw [prod_insert he,h,hea,pow_succ,mul_comm]
lemma ScaleState.pm_card (s : ScaleState G j) (a : SourceMarked s.activity K) :
    a.1.val.card≤ Fintype.card (SourceVertex (Fin G.n) K) := by
  let : Fintype (BagEdge (sourceBags s.activity K)) := Fintype.ofFinite _
  apply PM.card_le_vertices
  intro e
  exact ⟨e.val.val.1.out.1,by
    change e.val.val.1.out.1∈e.val.val.1
    exact Sym2.out_fst_mem _⟩
lemma ScaleState.observable_power (s : ScaleState G j) (a : SourceMarked s.activity K) :
    (observableA s.activity K a=0 ∨ observableA s.activity K a=1) ∧
    (observableD s.activity s.nextActivity K a=0 ∨
      ∃ t≤Fintype.card (SourceVertex (Fin G.n) K),observableD s.activity s.nextActivity K a=Trial.cooling G.n^t) ∧
    (∀ e₀,observableProbe s.activity s.nextActivity K e₀ a=0 ∨
      ∃ t≤Fintype.card (SourceVertex (Fin G.n) K),observableProbe s.activity s.nextActivity K e₀ a=Trial.cooling G.n^t) := by
  refine ⟨?_,?_,?_⟩
  · unfold observableA
    split_ifs <;> simp
  · unfold observableD
    split_ifs
    · right
      obtain ⟨t,ht,he⟩ := product_binary_power a.1.val _ (Trial.cooling G.n) (fun e _=>s.bag_reweight e)
      exact ⟨t,ht.trans (s.pm_card a),he⟩
    · exact Or.inl rfl
  · intro e₀
    unfold observableProbe
    split_ifs
    · right
      obtain ⟨t,ht,he⟩ := product_binary_power (a.1.val\{centralEdge s.activity K e₀}) _
        (Trial.cooling G.n) (fun e _=>s.bag_reweight e)
      refine ⟨t,ht.trans ((card_le_card sdiff_subset).trans (s.pm_card a)),?_⟩
      convert he using 1
      congr 1
      ext e
      simp only [mem_sdiff,mem_singleton]
    · exact Or.inl rfl
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
open Finset

def GridFraction (Q : ℕ) (x : ℝ) : Prop := ∃ a : ℕ,a≤Q ∧ x=(a:ℝ)/Q
lemma GridFraction.zero (Q : ℕ) : GridFraction Q 0 := ⟨0,Nat.zero_le _,by simp⟩
lemma GridFraction.one {Q : ℕ} (hQ : 0<Q) : GridFraction Q 1 :=
  ⟨Q,le_rfl,(div_self (by exact_mod_cast hQ.ne')).symm⟩
lemma GridFraction.fractionBound {Q : ℕ} {x : ℝ} (hQ : 0<Q) (h : GridFraction Q x) :
    FractionBound Q x := by
  obtain ⟨a,ha,he⟩ := h
  exact ⟨a,Q,hQ,ha,le_rfl,he⟩
lemma GridFraction.average {Ω : Type*} {S Q : ℕ} (f : Ω → ℝ) (x : Fin S → Ω)
    (h : ∀ i,GridFraction Q (f (x i))) :
    GridFraction (S*Q) (Enlargement.sampleAverage f x) := by
  classical
  choose a ha he using h
  refine ⟨∑ i,a i,?_,?_⟩
  · calc
      _ ≤ ∑ _i : Fin S,Q := sum_le_sum fun i _=>ha i
      _ = S*Q := by simp
  · unfold Enlargement.sampleAverage
    simp_rw [he]
    rw [← sum_div]
    push_cast
    ring
lemma GridFraction.cooling_power (n N t : ℕ) (ht : t≤N) :
    GridFraction ((n+1)^N) (((n:ℝ)/(n+1))^t) := by
  refine ⟨n^t*(n+1)^(N-t),?_,?_⟩
  · calc
      _ ≤ (n+1)^t*(n+1)^(N-t) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n+1)^N := by rw [←pow_add,Nat.add_sub_of_le ht]
  · have hpos : (0:ℝ)<n+1 := by positivity
    have he : ((n+1:ℕ):ℝ)=n+1 := by push_cast; rfl
    push_cast
    rw [div_pow,show N=t+(N-t) from (Nat.add_sub_of_le ht).symm,pow_add]
    field_simp
    congr 2
    omega

lemma FractionBound.pow {B : ℕ} {x : ℝ} (h : FractionBound B x) (k : ℕ) :
    FractionBound (B^k) (x^k) := by
  induction k with
  | zero => simpa using FractionBound.one (B:=1) le_rfl
  | succ k ih => simpa [pow_succ] using ih.mul h
lemma FractionBound.prod {ι : Type*} (A : Finset ι) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈A,FractionBound B (f i)) : FractionBound (B^A.card) (∏ i∈A,f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using FractionBound.one (B:=1) le_rfl
  | @insert i A hi ih =>
    simpa [prod_insert hi,card_insert_of_notMem hi,pow_succ,Nat.mul_comm] using
      (h i (mem_insert_self _ _)).mul (ih (fun j hj=>h j (mem_insert_of_mem hj)))
end MatchingFPRAS.BitArithmetic

end OAI
