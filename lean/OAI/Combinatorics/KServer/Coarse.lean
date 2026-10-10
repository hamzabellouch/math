import Mathlib
import OAI.Combinatorics.KServer.RankProportions

namespace OAI

noncomputable section
open scoped BigOperators
open Finset

namespace KServer.CoarseSchedule
open Finset

structure State where
  active : Bool
  value : ℝ

def Valid (s : State) : Prop := 0 ≤ s.value ∧ (s.active = false → s.value = 0)

noncomputable def update (c δ x : ℝ) (s : State) : State :=
  if s.active then
    if x ≤ 2*c then ⟨false,0⟩
    else if (1+δ)*s.value < x ∨ (1+δ)*x < s.value then ⟨true,x⟩ else s
  else if 5*c ≤ x then ⟨true,x⟩ else s

noncomputable def charge (s t : State) : ℝ := if s.value = t.value then 0 else s.value+t.value
noncomputable def factor (δ : ℝ) : ℝ := 1+2/δ
noncomputable def potential (c δ x : ℝ) (s : State) : ℝ :=
  factor δ * |x-s.value| + (if s.active then 2*(factor δ+1)*c else 0)

lemma factor_ge_seven (δ : ℝ) (hδ : 0 < δ) (hδu : δ ≤ 1/3) : 7 ≤ factor δ := by
  have hh : 6 ≤ 2/δ := (le_div_iff₀ hδ).mpr (by linarith)
  exact by dsimp [factor]; linarith

lemma update_valid {s : State} (hs : Valid s) {c δ x : ℝ} (hx : 0 ≤ x) :
    Valid (update c δ x s) := by
  unfold update
  split_ifs <;> simp_all [Valid]

lemma charge_self (s : State) : charge s s = 0 := by simp [charge]
lemma charge_le {s t : State} (hs : 0 ≤ s.value) (ht : 0 ≤ t.value) :
    charge s t ≤ s.value+t.value := by
  unfold charge
  split_ifs <;> linarith

lemma update_credit {c δ x : ℝ} {s : State} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hδu : δ ≤ 1/3) (hx : 0 ≤ x) (hs : Valid s) :
    charge s (update c δ x s) + potential c δ x (update c δ x s) ≤ potential c δ x s := by
  have hC := factor_ge_seven δ hδ hδu
  have hC0 : 0 ≤ factor δ := by linarith
  have hC1 : 1 ≤ factor δ := by linarith
  have hCs : |x-s.value| ≤ factor δ*|x-s.value| := by nlinarith [abs_nonneg (x-s.value)]
  unfold update
  split_ifs with hon hoff href hon'
  · have hsx : s.value ≤ |x-s.value|+x := by
      have hh := le_abs_self (s.value-x)
      rw [abs_sub_comm s.value x] at hh
      linarith
    have hch := charge_le (s := s) (t := ⟨false,0⟩) hs.1 (by norm_num)
    simp only [potential, Bool.false_eq_true, ite_false, sub_zero, abs_of_nonneg hx]
    simp only [hon, ite_true]
    have hbound : (factor δ+1)*x ≤ 2*(factor δ+1)*c := by
      nlinarith [mul_le_mul_of_nonneg_left hoff (show 0 ≤ factor δ+1 by linarith)]
    linarith
  · have hch := charge_le (s := s) (t := ⟨true,x⟩) hs.1 hx
    have hfac := RankTracking.factor_change_charge hs.1 hx hδ href
    rw [abs_sub_comm] at hfac
    change s.value+x ≤ factor δ*|x-s.value| at hfac
    simp only [potential, sub_self, abs_zero, mul_zero, zero_add, hon, ite_true]
    linarith
  · simp [charge_self]
  · have hfalse : s.active = false := by simpa using hon
    have hz := hs.2 hfalse
    have hch := charge_le (s := s) (t := ⟨true,x⟩) hs.1 hx
    simp only [potential, sub_self, abs_zero, mul_zero, zero_add, hfalse, Bool.false_eq_true, ite_false, ite_true,
      hz, sub_zero, abs_of_nonneg hx]
    have hc1 : 2*(factor δ+1)*c ≤ (factor δ-1)*(5*c) := by nlinarith
    have hc2 : (factor δ-1)*(5*c) ≤ (factor δ-1)*x :=
      mul_le_mul_of_nonneg_left hon' (by linarith)
    simp only [hz] at hch
    linarith
  · simp [charge_self]

lemma potential_nonneg {c δ x : ℝ} {s : State} (hc : 0 ≤ c) (hδ : 0 < δ) :
    0 ≤ potential c δ x s := by
  unfold potential factor
  split_ifs <;> positivity

lemma potential_input {c δ x y : ℝ} (s : State) (hδ : 0 < δ) :
    potential c δ y s ≤ potential c δ x s + factor δ*|y-x| := by
  have h0 : 0 ≤ factor δ := by unfold factor; positivity
  have hh := mul_le_mul_of_nonneg_left (abs_sub_le y x s.value) h0
  simpa only [potential, mul_add] using (show
    factor δ*|y-s.value|+(if s.active then 2*(factor δ+1)*c else 0) ≤
    factor δ*|x-s.value|+(if s.active then 2*(factor δ+1)*c else 0)+factor δ*|y-x| by
      linarith)

noncomputable def run (c δ : ℝ) (x : ℕ → ℝ) (initial : State) : ℕ → State
  | 0 => initial
  | t+1 => update c δ (x (t+1)) (run c δ x initial t)

lemma run_valid {c δ : ℝ} {x : ℕ → ℝ} {initial : State}
    (hx : ∀ t, 0 ≤ x t) (hi : Valid initial) : ∀ t, Valid (run c δ x initial t)
  | 0 => hi
  | t+1 => update_valid (run_valid hx hi t) (hx (t+1))

/-- Uniform-in-horizon amortization of the literal §03 active-size schedule.
This pays genuine old-plus-new charges, not merely total variation. -/
theorem active_size_budget {c δ : ℝ} {x : ℕ → ℝ} {initial : State}
    (hc : 0 ≤ c) (hδ : 0 < δ) (hδu : δ ≤ 1/3)
    (hx : ∀ t, 0 ≤ x t) (hi : Valid initial) (N : ℕ) :
    (∑ t ∈ range N, charge (run c δ x initial t) (run c δ x initial (t+1))) ≤
      factor δ*(∑ t ∈ range N, |x (t+1)-x t|) + potential c δ (x 0) initial := by
  have hstrong : (∑ t ∈ range N, charge (run c δ x initial t) (run c δ x initial (t+1))) +
      potential c δ (x N) (run c δ x initial N) ≤
      factor δ*(∑ t ∈ range N, |x (t+1)-x t|) + potential c δ (x 0) initial := by
    induction N with
    | zero => simp [run]
    | succ N ih =>
      have hcredit := update_credit hc hδ hδu (hx (N+1)) (run_valid (c := c) (δ := δ) hx hi N)
      have hinput := potential_input (c := c) (δ := δ) (x := x N) (y := x (N+1))
        (run c δ x initial N) hδ
      simp only [sum_range_succ, mul_add, run] at *
      linarith
  linarith [potential_nonneg (x := x N) (s := run c δ x initial N) hc hδ]

end KServer.CoarseSchedule


/-! The actual epoch/wholesale recurrence of §03. The old credit is discarded
on a parent refresh, never spent twice. Empty transitions are forced by the
same variation test. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.EpochSchedule
variable {J K : Type*} [Fintype J]

def total (x : J → ℝ) : ℝ := ∑ i, x i
def variation (x y : J → ℝ) : ℝ := ∑ i, |x i-y i|
lemma variation_nonneg (x y : J → ℝ) : 0 ≤ variation x y := sum_nonneg fun _ _ => abs_nonneg _
lemma total_nonneg {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ total x := sum_nonneg fun _ _ => hx _
lemma total_change (x y : J → ℝ) : |total x-total y| ≤ variation x y := by
  rw [total,total,←sum_sub_distrib]
  exact abs_sum_le_sum_abs _ _
lemma coordinate_change (x y : J → ℝ) (i : J) : |x i-y i| ≤ variation x y :=
  single_le_sum (fun j _ => abs_nonneg (x j-y j)) (mem_univ i)
lemma variation_triangle (x y z : J → ℝ) : variation x z ≤ variation x y+variation y z := by
  rw [variation,variation,variation,←sum_add_distrib]
  exact sum_le_sum fun i _ => abs_sub_le _ _ _

structure State (J : Type*) where
  reference : J → ℝ
  credit : ℝ

def Valid (x : J → ℝ) (s : State J) : Prop :=
  (∀ i, 0 ≤ s.reference i) ∧ 0 ≤ s.credit ∧ s.credit ≤ total s.reference/100 ∧
    variation x s.reference ≤ s.credit

def reset (x y : J → ℝ) (a b : K) (s : State J) : Prop :=
  a≠b ∨ total s.reference/100 < s.credit+variation y x

instance (x y : J → ℝ) (a b : K) (s : State J) : Decidable (reset x y a b s) := Classical.propDecidable _

def update (x y : J → ℝ) (a b : K) (s : State J) : State J :=
  if reset x y a b s then ⟨y,0⟩ else ⟨s.reference,s.credit+variation y x⟩

lemma update_valid {x y : J → ℝ} {a b : K} {s : State J}
    (hy : ∀ i, 0 ≤ y i) (hs : Valid x s) : Valid y (update x y a b s) := by
  unfold update
  split_ifs with hr
  · refine ⟨hy,le_rfl,div_nonneg (total_nonneg hy) (by norm_num),?_⟩
    simp [variation]
  · have hh := not_or.mp hr
    refine ⟨hs.1,add_nonneg hs.2.1 (variation_nonneg _ _),le_of_not_gt hh.2,?_⟩
    exact (variation_triangle y x s.reference).trans (by linarith [hs.2.2.2])

lemma valid_total {x : J → ℝ} {s : State J} (hs : Valid x s) :
    (99/100:ℝ)*total s.reference ≤ total x ∧ total x ≤ (101/100:ℝ)*total s.reference := by
  have hd := (abs_le.mp ((total_change x s.reference).trans hs.2.2.2))
  constructor <;> linarith [hs.2.2.1]

lemma valid_coordinate {x : J → ℝ} {s : State J} (hs : Valid x s) (i : J) :
    s.reference i-total s.reference/100 ≤ x i ∧ x i ≤ s.reference i+total s.reference/100 := by
  have hd := abs_le.mp ((coordinate_change x s.reference i).trans hs.2.2.2)
  constructor <;> linarith [hs.2.2.1]

lemma empty_transition {x y : J → ℝ} {a b : K} {s : State J}
    (hs : Valid x s)
    (he : (total x=0 ∧ 0 < total y) ∨ (0 < total x ∧ total y=0)) : reset x y a b s := by
  apply Or.inr
  have ha := total_nonneg hs.1
  have ht := valid_total hs
  have hd := abs_le.mp (total_change y x)
  rcases he with he | he
  · have hz : total s.reference=0 := by linarith
    rw [hz]
    linarith [hs.2.1]
  · have hi := hs.2.2.1
    have hn := variation_nonneg y x
    have hp : 0 < total s.reference := by linarith
    linarith [hs.2.1]

def wholesale (x y : J → ℝ) (a b : K) (s : State J) : ℝ :=
  if reset x y a b s then total x+total y else 0

def parentCharge (x y : J → ℝ) (a b : K) : ℝ := by
  classical
  exact if a≠b then total x+total y else 0

/-- Each volume-triggered wholesale consumes only its epoch's accumulated
variation. The constant 203 is the literal bound used in the source. -/
lemma update_budget {x y : J → ℝ} {a b : K} {s : State J}
    (hs : Valid x s) :
    wholesale x y a b s+203*(update x y a b s).credit ≤
      203*s.credit+203*variation y x+parentCharge x y a b := by
  classical
  by_cases hk : a≠b
  · have hr : reset x y a b s := Or.inl hk
    simp only [wholesale,update,ite_eq_left hr,parentCharge,ite_eq_left hk]
    linarith [hs.2.1,variation_nonneg y x]
  · by_cases hv : total s.reference/100 < s.credit+variation y x
    · have hr : reset x y a b s := Or.inr hv
      simp only [wholesale,update,ite_eq_left hr,parentCharge,ite_eq_right hk]
      have ht := (valid_total hs).2
      have hd := (abs_le.mp (total_change y x)).2
      have hd' := variation_nonneg y x
      linarith [hs.2.1]
    · have hr : ¬reset x y a b s := not_or.mpr ⟨hk,hv⟩
      simp only [wholesale,update,ite_eq_right hr,parentCharge,ite_eq_right hk]
      ring_nf
      exact le_rfl

def run (x : ℕ → J → ℝ) (key : ℕ → K) : ℕ → State J
  | 0 => ⟨x 0,0⟩
  | t+1 => update (x t) (x (t+1)) (key t) (key (t+1)) (run x key t)

lemma run_valid (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) :
    ∀ t, Valid (x t) (run x key t) := by
  intro t
  induction t with
  | zero => refine ⟨hx 0,le_rfl,by exact div_nonneg (total_nonneg (hx 0)) (by norm_num),?_⟩; simp [run,variation]
  | succ t ih => exact update_valid (hx (t+1)) ih

/-- Deterministic finite-horizon wholesale budget, with no terminal charge and
no dependence on the horizon in its constants. -/
theorem wholesale_budget (x : ℕ → J → ℝ) (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (n : ℕ) :
    (∑ t ∈ range n, wholesale (x t) (x (t+1)) (key t) (key (t+1)) (run x key t)) ≤
      203*(∑ t ∈ range n, variation (x (t+1)) (x t))+
      ∑ t ∈ range n, parentCharge (x t) (x (t+1)) (key t) (key (t+1)) := by
  have hh : ∀ m, (∑ t ∈ range m, wholesale (x t) (x (t+1)) (key t) (key (t+1)) (run x key t))+
      203*(run x key m).credit ≤
      203*(∑ t ∈ range m, variation (x (t+1)) (x t))+
      ∑ t ∈ range m, parentCharge (x t) (x (t+1)) (key t) (key (t+1)) := by
    intro m
    induction m with
    | zero => simp [run]
    | succ m ih =>
      have hs := update_budget (a := key m) (b := key (m+1)) (y := x (m+1)) (run_valid x key hx m)
      change wholesale _ _ _ _ _+203*(run x key (m+1)).credit ≤ _ at hs
      simp only [sum_range_succ]
      linarith
  have hn := (run_valid x key hx n).2.1
  linarith [hh n]

/-- Exact dominant selection; the same reference, hence the same mark, is
held until a wholesale event. -/
def dominant (s : State J) : Option J :=
  if h : ∃ i, 0 < total s.reference ∧ (85/100:ℝ)*total s.reference ≤ s.reference i
  then some h.choose else none

lemma dominant_large {x : J → ℝ} {s : State J} {o : J} (hs : Valid x s)
    (ho : dominant s=some o) : (84/100:ℝ)*total s.reference ≤ x o := by
  unfold dominant at ho
  split_ifs at ho with h
  · have he : h.choose=o := Option.some.inj ho
    have hh := h.choose_spec
    rw [he] at hh
    linarith [(valid_coordinate hs o).1]

lemma regular_small {x : J → ℝ} {s : State J} {i : J} (hs : Valid x s)
    (hi : dominant s≠some i) : x i ≤ (86/100:ℝ)*total s.reference := by
  classical
  have ha := total_nonneg hs.1
  have hh : s.reference i ≤ (85/100:ℝ)*total s.reference := by
    by_cases hp : 0 < total s.reference
    · by_contra hle
      have hbig : (85/100:ℝ)*total s.reference ≤ s.reference i := le_of_lt (lt_of_not_ge hle)
      have hex : ∃ j, 0 < total s.reference ∧ (85/100:ℝ)*total s.reference ≤ s.reference j := ⟨i,hp,hbig⟩
      have heq : hex.choose=i := by
        by_contra hn
        have hsum := sum_le_sum_of_subset_of_nonneg (show ({hex.choose,i} : Finset J) ⊆ univ by simp)
          (fun j _ _ => hs.1 j)
        simp only [sum_pair hn] at hsum
        change s.reference hex.choose+s.reference i ≤ total s.reference at hsum
        linarith [hex.choose_spec.2]
      exact hi (by simp [dominant,hex,heq])
    · have hz : total s.reference=0 := le_antisymm (le_of_not_gt hp) ha
      have hb := single_le_sum (fun j _ => hs.1 j) (mem_univ i)
      change s.reference i ≤ total s.reference at hb
      rw [hz] at hb ⊢
      simpa using hb
  linarith [(valid_coordinate hs i).2]

lemma side_total [DecidableEq J] {x : J → ℝ} {s : State J} {o : J} (hs : Valid x s)
    (ho : dominant s=some o) : (∑ i ∈ univ.erase o, x i) ≤ (16/100:ℝ)*total s.reference := by
  classical
  have hr : (85/100:ℝ)*total s.reference ≤ s.reference o := by
    unfold dominant at ho
    split_ifs at ho with h
    · have he : h.choose=o := Option.some.inj ho
      simpa only [he] using h.choose_spec.2
  have hd : (∑ i ∈ univ.erase o, x i) ≤ (∑ i ∈ univ.erase o, s.reference i)+variation x s.reference := by
    calc _ ≤ (∑ i ∈ univ.erase o, s.reference i)+(∑ i ∈ univ.erase o, |x i-s.reference i|) := by
          rw [←sum_add_distrib]
          exact sum_le_sum fun i _ => by linarith [le_abs_self (x i-s.reference i)]
         _ ≤ _ := by
          have hn : (∑ i ∈ univ.erase o, |x i-s.reference i|) ≤ variation x s.reference :=
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _ => abs_nonneg _)
          exact add_le_add le_rfl hn
  have he := sum_erase_add univ s.reference (mem_univ o)
  change (∑ i ∈ univ.erase o, s.reference i)+s.reference o=total s.reference at he
  linarith [hs.2.2.1,hs.2.2.2]

end KServer.EpochSchedule

namespace KServer.CoarseProcess
open RankTracking RankFunctions CoarseSchedule
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Literal sum of the independently maintained size-rank references. -/
def estimate (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, sizeRank (held (factorTest sizeRank δ) (P a).p t ω)
def size (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, sizeRank ((P a).p t ω)

lemma estimate_nonneg (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ estimate δ P t ω := sum_nonneg fun _ _ => sizeRank_nonneg _
lemma size_nonneg (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ size P t ω := sum_nonneg fun _ _ => sizeRank_nonneg _

lemma estimate_accuracy {δ : ℝ} (hδ : 0 < δ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    size P t ω ≤ (1+δ)*estimate δ P t ω ∧
      estimate δ P t ω ≤ (1+δ)*size P t ω := by
  constructor
  · rw [estimate,mul_sum]
    apply sum_le_sum
    intro a _
    have hh := (factor_held_accurate sizeRank hδ (fun _ _ => sizeRank_nonneg _) (P a).range t ω).1
    exact (inv_mul_le_iff₀ (by linarith : 0 < 1+δ)).mp hh
  · rw [size,mul_sum]
    exact sum_le_sum fun a _ =>
      (factor_held_accurate sizeRank hδ (fun _ _ => sizeRank_nonneg _) (P a).range t ω).2

lemma estimate_bound (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    estimate δ P t ω ≤ Fintype.card R := by
  calc _ ≤ ∑ _ : R, (1:ℝ) := by
        apply sum_le_sum
        intro a _
        have hr := held_range (factorTest sizeRank δ) (P a).range t ω
        exact (sizeRank_le_complement hr).trans (by linarith [hr.1])
       _ = _ := by simp

lemma term_variation {δ : ℝ} (hδ : 0 < δ) (hδu : δ < 1/2)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (P : FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω =>
        |sizeRank (held (factorTest sizeRank δ) P.p (t+1) ω)-
          sizeRank (held (factorTest sizeRank δ) P.p t ω)|)) ≤
      (5*(4/3:ℝ)^2/δ)*((∑ t ∈ range N, avg w (fun ω => |P.p (t+1) ω-P.before (t+1) ω|))+1) := by
  have hlip (p q : ℝ) : |Real.sqrt (sizeRank p)-Real.sqrt (sizeRank q)| ≤ (4/3:ℝ)*|p-q| := by
    simpa only [Real.dist_eq,NNReal.coe_div,NNReal.coe_ofNat] using
      sqrt_sizeRank_lipschitz.dist_le_mul p q
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => (5*(4/3:ℝ)^2/δ)*credit (factorTest sizeRank δ) P.p t ω) :=
        sum_le_sum fun t _ => avg_mono hw (factor_movement_credit sizeRank hδ hδu (by norm_num)
          (fun _ _ => sizeRank_nonneg _) (fun p _ q _ => hlip p q) P.range t)
       _ = (5*(4/3:ℝ)^2/δ)*(∑ t ∈ range N, avg w (credit (factorTest sizeRank δ) P.p t)) := by
        simp_rw [avg_mul]; rw [mul_sum]
       _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (factorTest sizeRank δ) hw hw1 P N)
        (by positivity)

lemma estimate_variation {δ : ℝ} (hδ : 0 < δ) (hδu : δ < 1/2)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (P : R → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => |estimate δ P (t+1) ω-estimate δ P t ω|)) ≤
      (5*(4/3:ℝ)^2/δ)*
        ((∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+
          Fintype.card R) := by
  calc _ ≤ ∑ t ∈ range N, ∑ a, avg w (fun ω =>
        |sizeRank (held (factorTest sizeRank δ) (P a).p (t+1) ω)-
          sizeRank (held (factorTest sizeRank δ) (P a).p t ω)|) := by
        apply sum_le_sum
        intro t _
        rw [←avg_sum]
        apply avg_mono hw
        intro ω
        simp only [estimate,←sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
       _ = ∑ a, ∑ t ∈ range N, avg w (fun ω =>
        |sizeRank (held (factorTest sizeRank δ) (P a).p (t+1) ω)-
          sizeRank (held (factorTest sizeRank δ) (P a).p t ω)|) := by rw [sum_comm]
       _ ≤ ∑ a, (5*(4/3:ℝ)^2/δ)*
          ((∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+1) := by
        apply sum_le_sum
        intro a _
        exact term_variation hδ hδu hw hw1 (P a) N
       _ = _ := by simp only [mul_add,sum_add_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul]; ring

/-- All invariants are established after actually executing the hysteretic rule. -/
lemma update_accuracy {c δ x : ℝ} {s : CoarseSchedule.State}
    (hc : 0 < c) (hδ : 0 < δ) (hx : 0 ≤ x) (hs : CoarseSchedule.Valid s) :
    let a := CoarseSchedule.update c δ x s
    (a.active=true → 2*c < x ∧ x ≤ (1+δ)*a.value ∧ a.value ≤ (1+δ)*x) ∧
    (a.active=false → x < 5*c ∧ a.value=0) := by
  have he : x ≤ (1+δ)*x := by nlinarith [mul_nonneg hδ.le hx]
  cases ha : s.active with
  | false =>
    by_cases ht : 5*c ≤ x
    · simp only [CoarseSchedule.update,ha,Bool.false_eq_true,ite_false,ite_eq_left ht]
      simp only [Bool.true_eq_false, false_implies, and_true, true_implies]
      exact ⟨by linarith,he,he⟩
    · simp [CoarseSchedule.update,ha,ht,hs.2 ha,lt_of_not_ge ht]
  | true =>
    by_cases ht : x ≤ 2*c
    · simp [CoarseSchedule.update,ha,ht,show x < 5*c by linarith]
    · by_cases hf : (1+δ)*s.value < x ∨ (1+δ)*x < s.value
      · simp only [CoarseSchedule.update,ha,ite_true,ite_eq_right ht,ite_eq_left hf]
        simp only [Bool.true_eq_false,false_implies,and_true,true_implies]
        exact ⟨lt_of_not_ge ht,he,he⟩
      · simp only [CoarseSchedule.update,ha,ite_true,ite_eq_right ht,ite_eq_right hf]
        simp only [Bool.true_eq_false,false_implies,and_true,true_implies]
        have hh := not_or.mp hf
        exact ⟨lt_of_not_ge ht,le_of_not_gt hh.1,le_of_not_gt hh.2⟩

/-- Trackers are not reinitialized; the active state alone is updated. -/
def active (c δ : ℝ) (P : R → FilteredRanks w) (ω : Ω) : ℕ → CoarseSchedule.State :=
  CoarseSchedule.run c δ (fun t => estimate δ P t ω)
    (CoarseSchedule.update c δ (estimate δ P 0 ω) ⟨false,0⟩)

lemma active_valid (c δ : ℝ) (P : R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    CoarseSchedule.Valid (active c δ P ω t) :=
  run_valid (fun t => estimate_nonneg δ P t ω)
    (update_valid (by simp [CoarseSchedule.Valid]) (estimate_nonneg δ P 0 ω)) t

lemma active_accuracy {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    let a := active c δ P ω t
    (a.active=true → (9/10)*size P t ω ≤ a.value ∧ a.value ≤ (11/10)*size P t ω ∧ c ≤ size P t ω) ∧
    (10*c ≤ size P t ω → a.active=true) := by
  have hx := estimate_nonneg δ P t ω
  have hm := size_nonneg P t ω
  have hh : let a := active c δ P ω t
      (a.active=true → 2*c < estimate δ P t ω ∧ estimate δ P t ω ≤ (1+δ)*a.value ∧
        a.value ≤ (1+δ)*estimate δ P t ω) ∧
      (a.active=false → estimate δ P t ω < 5*c ∧ a.value=0) := by
    cases t with
    | zero => exact update_accuracy hc hδ hx (by simp [CoarseSchedule.Valid])
    | succ t => exact update_accuracy hc hδ hx (active_valid c δ P ω t)
  have hrough : (1+δ)^2 ≤ 11/10 := by nlinarith [sq_nonneg (δ-1/1000)]
  have hs := estimate_accuracy hδ P t ω
  have hav : 0 ≤ (active c δ P ω t).value := (active_valid c δ P ω t).1
  constructor
  · intro ha
    have h := hh.1 ha
    have hmul₁ := mul_le_mul_of_nonneg_left h.2.1 (by linarith : 0 ≤ 1+δ)
    have hmul₂ := mul_le_mul_of_nonneg_left hs.2 (by linarith : 0 ≤ 1+δ)
    have hbound := mul_le_mul_of_nonneg_right hrough hav
    have hbound₂ := mul_le_mul_of_nonneg_right hrough hm
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1-δ) hm]
  · intro hM
    by_contra hn
    have hf : (active c δ P ω t).active=false := Bool.eq_false_of_not_eq_true hn
    have hhf := hh.2 hf
    have hmul := mul_le_mul_of_nonneg_right (show 1+δ ≤ 2 by linarith) hx
    nlinarith


lemma charge_nonneg {s t : CoarseSchedule.State} (hs : CoarseSchedule.Valid s)
    (ht : CoarseSchedule.Valid t) : 0 ≤ CoarseSchedule.charge s t := by
  unfold CoarseSchedule.charge
  split_ifs
  · rfl
  · exact add_nonneg hs.1 ht.1

lemma initial_potential {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/3)
    (P : R → FilteredRanks w) (ω : Ω) :
    potential c δ (estimate δ P 0 ω) (active c δ P ω 0) ≤ factor δ*Fintype.card R := by
  have hi : CoarseSchedule.Valid ⟨false,0⟩ := by simp [CoarseSchedule.Valid]
  have hx := estimate_nonneg δ P 0 ω
  have hh := update_credit hc.le hδ hδu hx hi
  have hn := charge_nonneg hi (update_valid hi hx (c:=c) (δ:=δ))
  have hb := mul_le_mul_of_nonneg_left (estimate_bound δ P 0 ω)
    (show 0 ≤ factor δ by unfold factor; positivity)
  have hp0 : CoarseSchedule.potential c δ (estimate δ P 0 ω) ⟨false,0⟩ = factor δ*estimate δ P 0 ω := by
    simp [CoarseSchedule.potential,abs_of_nonneg hx]
  change 0 ≤ charge ⟨false,0⟩ (active c δ P ω 0) at hn
  rw [hp0] at hh
  change CoarseSchedule.charge ⟨false,0⟩ (active c δ P ω 0)+
    potential c δ (estimate δ P 0 ω) (active c δ P ω 0) ≤ factor δ*estimate δ P 0 ω at hh
  linarith

lemma avg_range (w : Ω → ℝ) (f : ℕ → Ω → ℝ) (N : ℕ) :
    (∑ t ∈ range N, avg w (f t))=avg w (fun ω => ∑ t ∈ range N,f t ω) := by
  simp only [avg,mul_sum]
  exact sum_comm

/-- Actual old-plus-new active refresh budget, with a fixed-star endpoint. -/
theorem active_budget {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (P : R → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω =>
        charge (active c δ P ω t) (active c δ P ω (t+1)))) ≤
      (factor δ*(5*(4/3:ℝ)^2/δ)) *
        (∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+
      (factor δ*(5*(4/3:ℝ)^2/δ+1))*Fintype.card R := by
  have hf : 0 ≤ factor δ := by unfold factor; positivity
  have hs (ω : Ω) := active_size_budget hc.le hδ (show δ ≤ 1/3 by linarith)
    (fun t => estimate_nonneg δ P t ω)
    (update_valid (show CoarseSchedule.Valid ⟨false,0⟩ by simp [CoarseSchedule.Valid])
      (estimate_nonneg δ P 0 ω) (c:=c) (δ:=δ)) N
  have hb (ω : Ω) := initial_potential hc hδ (show δ ≤ 1/3 by linarith) P ω
  have hs' (ω : Ω) : (∑ t ∈ range N, charge (active c δ P ω t) (active c δ P ω (t+1))) ≤
      factor δ*(∑ t ∈ range N, |estimate δ P (t+1) ω-estimate δ P t ω|)+
      potential c δ (estimate δ P 0 ω) (active c δ P ω 0) := hs ω
  have hh := avg_mono hw (fun ω => hs' ω |>.trans (add_le_add_right (hb ω) _))
  change avg w (fun ω => ∑ t ∈ range N, charge (active c δ P ω t) (active c δ P ω (t+1))) ≤
    avg w (fun ω => factor δ * (∑ t ∈ range N, |estimate δ P (t+1) ω-estimate δ P t ω|)+
      factor δ*Fintype.card R) at hh
  rw [avg_add,avg_mul,avg_const w hw1,←avg_range,←avg_range] at hh
  have hv := mul_le_mul_of_nonneg_left (estimate_variation hδ (by linarith) hw hw1 P N) hf
  exact hh.trans (by nlinarith)

lemma estimate_adapted (δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ a t ω, (P a).history t ω=H t ω) (t : ℕ) :
    Adapted (H t) (estimate δ P t) := by
  intro ω z he
  unfold estimate
  apply sum_congr rfl
  intro a _
  rw [held_adapted (factorTest sizeRank δ) (P a) t ω z (by simpa only [hH] using he)]

lemma active_adapted (c δ : ℝ) (P : R → FilteredRanks w) (H : ℕ → Ω → ℕ)
    (hH : ∀ a t ω, (P a).history t ω=H t ω)
    (href : ∀ t ω z, H (t+1) ω=H (t+1) z → H t ω=H t z) (t : ℕ) :
    ∀ ω z, H t ω=H t z → active c δ P ω t=active c δ P z t := by
  induction t with
  | zero =>
    intro ω z he
    simp only [active,run]
    rw [estimate_adapted δ P H hH 0 ω z he]
  | succ t ih =>
    intro ω z he
    change update c δ (estimate δ P (t+1) ω) (active c δ P ω t)=
      update c δ (estimate δ P (t+1) z) (active c δ P z t)
    rw [estimate_adapted δ P H hH (t+1) ω z he,ih ω z (href t ω z he)]

/-- The parent's scalar relative reference, and later the side-total reference,
use exactly the manuscript's two-sided factor test, including zero crossings. -/
def relative (δ : ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := held (factorTest id δ) x

omit [Fintype Ω] in
lemma relative_nonneg {δ : ℝ} (x : ℕ → Ω → ℝ) (hx : ∀ t ω, 0 ≤ x t ω) (t : ℕ) (ω : Ω) :
    0 ≤ relative δ x t ω := by
  induction t with
  | zero => exact hx 0 ω
  | succ t ih =>
    simp only [relative,held]
    split_ifs
    · exact hx (t+1) ω
    · exact ih

omit [Fintype Ω] in
lemma relative_accuracy {δ : ℝ} (hδ : 0 < δ) (x : ℕ → Ω → ℝ)
    (hx : ∀ t ω, 0 ≤ x t ω) (t : ℕ) (ω : Ω) :
    x t ω ≤ (1+δ)*relative δ x t ω ∧ relative δ x t ω ≤ (1+δ)*x t ω := by
  have he (y : ℝ) (hy : 0 ≤ y) : y ≤ (1+δ)*y := by nlinarith [mul_nonneg hδ.le hy]
  cases t with
  | zero => exact ⟨he _ (hx _ _),he _ (hx _ _)⟩
  | succ t =>
    simp only [relative,held]
    split_ifs with ht
    · exact ⟨he _ (hx _ _),he _ (hx _ _)⟩
    · simp only [factorTest,id_eq,not_or,not_lt] at ht
      exact ⟨ht.2,ht.1⟩

def relativeCharge (δ : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if relative δ x t ω=relative δ x (t+1) ω then 0 else
    relative δ x t ω+relative δ x (t+1) ω

omit [Fintype Ω] in
lemma relative_charge_bound {δ : ℝ} (hδ : 0 < δ) (x : ℕ → Ω → ℝ)
    (hx : ∀ t ω, 0 ≤ x t ω) (t : ℕ) (ω : Ω) :
    relativeCharge δ x t ω ≤ factor δ*|relative δ x (t+1) ω-relative δ x t ω| := by
  by_cases ht : factorTest id δ (x (t+1) ω) (relative δ x t ω)
  · have he : relative δ x (t+1) ω=x (t+1) ω := by
      change (if factorTest id δ (x (t+1) ω) (relative δ x t ω) then x (t+1) ω else relative δ x t ω)=_
      exact ite_eq_left ht
    have hh := factor_change_charge (hx (t+1) ω) (relative_nonneg x hx t ω) hδ ht
    rw [relativeCharge,he]
    split_ifs
    · exact mul_nonneg (by unfold factor; positivity) (abs_nonneg _)
    · unfold factor; linarith
  · have he : relative δ x (t+1) ω=relative δ x t ω := by
      change (if factorTest id δ (x (t+1) ω) (relative δ x t ω) then x (t+1) ω else relative δ x t ω)=_
      exact ite_eq_right ht
    simp [relativeCharge,he]

omit [Fintype Ω] in
lemma relative_budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → Ω → ℝ)
    (hx : ∀ t ω, 0 ≤ x t ω) (N : ℕ) (ω : Ω) :
    (∑ t ∈ range N, relativeCharge δ x t ω) ≤
      factor δ*(∑ t ∈ range N, |x (t+1) ω-x t ω|) := by
  calc _ ≤ ∑ t ∈ range N, factor δ*|relative δ x (t+1) ω-relative δ x t ω| :=
        sum_le_sum fun t _ => relative_charge_bound hδ x hx t ω
       _ = factor δ*(∑ t ∈ range N, |relative δ x (t+1) ω-relative δ x t ω|) := (mul_sum _ _ _).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (held_variation (factorTest id δ) x N ω)
        (by unfold factor; positivity)

end KServer.CoarseProcess

end
end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseEpoch
open RankTracking CoarseSchedule CoarseProcess
variable {Ω R J : Type} [Fintype Ω] [Fintype R] [Fintype J]
variable {w : Ω → ℝ}

def clipped (c δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  max c (estimate δ P t ω)

def parent (c δ : ℝ) (P : R → FilteredRanks w) : ℕ → Ω → ℝ :=
  relative δ (clipped c δ P)

lemma clipped_nonneg {c : ℝ} (hc : 0 ≤ c) (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ clipped c δ P t ω := hc.trans (le_max_left _ _)

lemma clipped_variation (c δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    |clipped c δ P (t+1) ω-clipped c δ P t ω| ≤ |estimate δ P (t+1) ω-estimate δ P t ω| := by
  unfold clipped
  simpa only [max_comm c] using abs_max_sub_max_le_abs (estimate δ P (t+1) ω) (estimate δ P t ω) c

lemma clipped_accuracy {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    max c (size P t ω) ≤ (1+δ)*clipped c δ P t ω ∧
      clipped c δ P t ω ≤ (1+δ)*max c (size P t ω) := by
  have h := estimate_accuracy hδ P t ω
  have he : 0 ≤ 1+δ := by linarith
  have hcc : c ≤ (1+δ)*c := by nlinarith [mul_nonneg hδ.le hc]
  constructor
  · apply max_le
    · exact hcc.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) he)
    · exact h.1.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) he)
  · apply max_le
    · exact (le_max_left _ _).trans (by nlinarith [mul_nonneg hδ.le (hc.trans (le_max_left c (size P t ω)))])
    · exact h.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) he)

lemma parent_accuracy {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ)
    (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    max c (size P t ω) ≤ (1+δ)^2*parent c δ P t ω ∧
      parent c δ P t ω ≤ (1+δ)^2*max c (size P t ω) := by
  have ha := clipped_accuracy hc hδ P t ω
  have hb := relative_accuracy hδ (clipped c δ P) (clipped_nonneg hc δ P) t ω
  change clipped c δ P t ω ≤ (1+δ)*parent c δ P t ω ∧ parent c δ P t ω ≤ (1+δ)*clipped c δ P t ω at hb
  have he : 0 ≤ 1+δ := by linarith
  constructor
  · exact ha.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hb.1 he])
  · exact hb.2.trans (by nlinarith [mul_le_mul_of_nonneg_left ha.2 he])

lemma parent_nonneg {c : ℝ} (hc : 0 ≤ c) (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ parent c δ P t ω := relative_nonneg _ (clipped_nonneg hc δ P) t ω

lemma parent_budget {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hδu : δ ≤ 1/3)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω,w ω=1) (P : R → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (relativeCharge δ (clipped c δ P) t)) ≤
      (factor δ*(5*(4/3:ℝ)^2/δ))*
        ((∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+Fintype.card R) := by
  have hf : 0 ≤ factor δ := by unfold factor; positivity
  rw [avg_range]
  calc _ ≤ avg w (fun ω => factor δ*(∑ t ∈ range N, |estimate δ P (t+1) ω-estimate δ P t ω|)) := by
        apply avg_mono hw
        intro ω
        exact (relative_budget hδ _ (clipped_nonneg hc δ P) N ω).trans
          (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => clipped_variation c δ P t ω) hf)
       _ = factor δ*(∑ t ∈ range N, avg w (fun ω => |estimate δ P (t+1) ω-estimate δ P t ω|)) := by
        rw [avg_mul,←avg_range]
       _ ≤ _ := by
        calc _ ≤ factor δ*((5*(4/3:ℝ)^2/δ)*
            ((∑ a, ∑ t ∈ range N, avg w (fun ω => |(P a).p (t+1) ω-(P a).before (t+1) ω|))+Fintype.card R)) :=
            mul_le_mul_of_nonneg_left (CoarseProcess.estimate_variation hδ (by linarith) hw hw1 P N) hf
             _ = _ := by ring

def vector (c δ : ℝ) (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) : J → ℝ :=
  fun i => (active c δ (P i) ω t).value

omit [Fintype J] in
lemma vector_nonneg (c δ : ℝ) (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) (i : J) :
    0 ≤ vector c δ P ω t i := (active_valid c δ (P i) ω t).1

lemma value_bound {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    (active c δ P ω t).value ≤ (11/10)*size P t ω := by
  cases ha : (active c δ P ω t).active with
  | true => exact ((active_accuracy hc hδ hδu P ω t).1 ha).2.1
  | false => rw [(active_valid c δ P ω t).2 ha]; exact mul_nonneg (by norm_num) (size_nonneg P t ω)

lemma total_parent {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hε : 0 < ε) (hεu : ε ≤ 1/1000) (P : J → R → FilteredRanks w) (V : R → FilteredRanks w)
    (htree : ∀ t ω, (∑ i,size (P i) t ω) ≤ size V t ω) (ω : Ω) (t : ℕ) :
    EpochSchedule.total (vector c δ P ω t) ≤ 2*parent c ε V t ω := by
  have h := parent_accuracy hc.le hε V t ω
  have hp := parent_nonneg hc.le ε V t ω
  have hsq : (11/10:ℝ)*(1+ε)^2 ≤ 2 := by nlinarith [sq_nonneg (ε-1/1000)]
  calc _ ≤ ∑ i, (11/10:ℝ)*size (P i) t ω := sum_le_sum fun i _ => value_bound hc hδ hδu (P i) ω t
       _ = (11/10:ℝ)*(∑ i,size (P i) t ω) := (mul_sum _ _ _).symm
       _ ≤ (11/10:ℝ)*size V t ω := mul_le_mul_of_nonneg_left (htree t ω) (by norm_num)
       _ ≤ (11/10:ℝ)*((1+ε)^2*parent c ε V t ω) :=
          mul_le_mul_of_nonneg_left ((le_max_right _ _).trans h.1) (by norm_num)
       _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsq hp]

lemma value_variation {s t : CoarseSchedule.State} (hs : CoarseSchedule.Valid s) (ht : CoarseSchedule.Valid t) :
    |s.value-t.value| ≤ charge s t := by
  unfold charge
  split_ifs with he
  · simp [he]
  · exact abs_sub_le_iff.mpr ⟨by linarith [ht.1],by linarith [hs.1]⟩

lemma vector_variation (c δ : ℝ) (P : J → R → FilteredRanks w) (ω : Ω) (t : ℕ) :
    EpochSchedule.variation (vector c δ P ω (t+1)) (vector c δ P ω t) ≤
      ∑ i, charge (active c δ (P i) ω t) (active c δ (P i) ω (t+1)) := by
  apply sum_le_sum
  intro i _
  rw [abs_sub_comm]
  exact value_variation (active_valid c δ (P i) ω t) (active_valid c δ (P i) ω (t+1))

lemma wholesale_parent {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hε : 0 < ε) (hεu : ε ≤ 1/1000) (P : J → R → FilteredRanks w) (V : R → FilteredRanks w)
    (htree : ∀ t ω, (∑ i,size (P i) t ω) ≤ size V t ω) (β : ℝ → ℝ) (ω : Ω) (t : ℕ) :
    EpochSchedule.parentCharge (vector c δ P ω t) (vector c δ P ω (t+1))
        (β (parent c ε V t ω)) (β (parent c ε V (t+1) ω)) ≤
      2*relativeCharge ε (clipped c ε V) t ω := by
  classical
  unfold EpochSchedule.parentCharge
  split_ifs with he
  · have hn : parent c ε V t ω≠parent c ε V (t+1) ω := fun hh => he (congrArg β hh)
    change _ ≤ 2*(if parent c ε V t ω=parent c ε V (t+1) ω then 0 else parent c ε V t ω+parent c ε V (t+1) ω)
    rw [ite_eq_right hn]
    linarith [total_parent hc hδ hδu hε hεu P V htree ω t,
      total_parent hc hδ hδu hε hεu P V htree ω (t+1)]
  · unfold relativeCharge
    split_ifs
    · norm_num
    · exact mul_nonneg (by norm_num) (add_nonneg (parent_nonneg hc.le ε V t ω) (parent_nonneg hc.le ε V (t+1) ω))

/-- The literal epoch recurrence is paid by actual active-size and parent
reference changes; the test does not assume its own amortized conclusion. -/
lemma wholesale_budget {c δ ε : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hε : 0 < ε) (hεu : ε ≤ 1/1000) (P : J → R → FilteredRanks w) (V : R → FilteredRanks w)
    (htree : ∀ t ω, (∑ i,size (P i) t ω) ≤ size V t ω) (β : ℝ → ℝ) (ω : Ω) (N : ℕ) :
    (∑ t ∈ range N, EpochSchedule.wholesale (vector c δ P ω t) (vector c δ P ω (t+1))
        (β (parent c ε V t ω)) (β (parent c ε V (t+1) ω))
        (EpochSchedule.run (vector c δ P ω) (fun t => β (parent c ε V t ω)) t)) ≤
      203*(∑ t ∈ range N, ∑ i,charge (active c δ (P i) ω t) (active c δ (P i) ω (t+1)))+
      2*(∑ t ∈ range N, relativeCharge ε (clipped c ε V) t ω) := by
  have hb := EpochSchedule.wholesale_budget (vector c δ P ω) (fun t => β (parent c ε V t ω))
    (vector_nonneg c δ P ω) N
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => vector_variation c δ P ω t) (by norm_num))
    (by rw [mul_sum]; exact sum_le_sum fun t _ => wholesale_parent hc hδ hδu hε hεu P V htree β ω t))

end KServer.CoarseEpoch

end


noncomputable section
open scoped BigOperators
open Finset
local instance (p : Prop) : Decidable p := Classical.propDecidable p
namespace KServer.CoarseSide
open RankTracking CoarseSchedule EpochSchedule

/-- Relative reference with genuine wholesale resets. Resetting discards,
rather than spends, the unused scalar variation credit. -/
def held (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Prop) : ℕ → ℝ
  | 0 => x 0
  | t+1 => if reset t ∨ factorTest id δ (x (t+1)) (held δ x reset t)
      then x (t+1) else held δ x reset t

lemma held_nonneg (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Prop) (hx : ∀ t, 0 ≤ x t) (t : ℕ) :
    0 ≤ held δ x reset t := by
  induction t with
  | zero => exact hx 0
  | succ t ih => simp only [held]; split_ifs; exact hx (t+1); exact ih

lemma held_accuracy {δ : ℝ} (hδ : 0 < δ) (x : ℕ → ℝ) (reset : ℕ → Prop)
    (hx : ∀ t, 0 ≤ x t) (t : ℕ) :
    x t ≤ (1+δ)*held δ x reset t ∧ held δ x reset t ≤ (1+δ)*x t := by
  have he (t : ℕ) : x t ≤ (1+δ)*x t := by nlinarith [mul_nonneg hδ.le (hx t)]
  cases t with
  | zero => exact ⟨he 0,he 0⟩
  | succ t =>
    simp only [held]
    split_ifs with hr
    · exact ⟨he (t+1),he (t+1)⟩
    · have hf := (not_or.mp hr).2
      simp only [factorTest,id_eq,not_or,not_lt] at hf
      exact ⟨hf.2,hf.1⟩

def charge (δ : ℝ) (x : ℕ → ℝ) (reset : ℕ → Prop) (t : ℕ) : ℝ :=
  if ¬reset t ∧ factorTest id δ (x (t+1)) (held δ x reset t) then x t+x (t+1) else 0

def stepVariation (x : ℕ → ℝ) (reset : ℕ → Prop) (t : ℕ) : ℝ :=
  if reset t then 0 else |x (t+1)-x t|

def C (δ : ℝ) : ℝ := (1+δ)*factor δ

lemma C_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ C δ := by unfold C factor; positivity

lemma update_budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → ℝ) (reset : ℕ → Prop)
    (hx : ∀ t, 0 ≤ x t) (t : ℕ) :
    charge δ x reset t+C δ*|x (t+1)-held δ x reset (t+1)| ≤
      C δ*|x t-held δ x reset t|+C δ*stepVariation x reset t := by
  have hC := C_nonneg hδ
  have hU := held_nonneg δ x reset hx t
  have ha := held_accuracy hδ x reset hx t
  by_cases hr : reset t
  · simp only [held,charge,not_true_eq_false,hr,false_and,true_or,ite_false,sub_self,abs_zero,mul_zero,add_zero,stepVariation,ite_true]
    exact mul_nonneg hC (abs_nonneg _)
  · by_cases hf : factorTest id δ (x (t+1)) (held δ x reset t)
    · have hp := factor_change_charge (hx (t+1)) hU hδ hf
      have hp' : x t+x (t+1) ≤ C δ*|x (t+1)-held δ x reset t| := by
        have he := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1+δ by linarith)
        have hh : x (t+1) ≤ (1+δ)*x (t+1) := by nlinarith [mul_nonneg hδ.le (hx (t+1))]
        unfold C factor
        change x (t+1)+held δ x reset t ≤ (1+2/δ)*|x (t+1)-held δ x reset t| at hp
        nlinarith
      simp only [held,charge,hr,not_false_eq_true,hf,and_self,or_true,ite_true,
        sub_self,abs_zero,mul_zero,add_zero,stepVariation,ite_false]
      exact hp'.trans (by nlinarith [mul_le_mul_of_nonneg_left (abs_sub_le (x (t+1)) (x t) (held δ x reset t)) hC])
    · simp only [held,charge,hr,not_false_eq_true,hf,and_false,false_or,ite_false,zero_add,stepVariation]
      nlinarith [mul_le_mul_of_nonneg_left (abs_sub_le (x (t+1)) (x t) (held δ x reset t)) hC]

lemma budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → ℝ) (reset : ℕ → Prop)
    (hx : ∀ t, 0 ≤ x t) (N : ℕ) :
    (∑ t ∈ range N, charge δ x reset t) ≤ C δ*(∑ t ∈ range N, stepVariation x reset t) := by
  have hh : (∑ t ∈ range N, charge δ x reset t)+C δ*|x N-held δ x reset N| ≤
      C δ*(∑ t ∈ range N, stepVariation x reset t) := by
    induction N with
    | zero => simp [held]
    | succ N ih =>
      have h := update_budget hδ x reset hx N
      rw [sum_range_succ,sum_range_succ,mul_add]
      linarith
  linarith [mul_nonneg (C_nonneg hδ) (abs_nonneg (x N-held δ x reset N))]

variable {J K : Type} [Fintype J]

def side (x : J → ℝ) (s : EpochSchedule.State J) : ℝ :=
  ∑ i, if dominant s=some i then 0 else if (dominant s).isSome then x i else 0

lemma side_nonneg {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) (s : EpochSchedule.State J) :
    0 ≤ side x s := by
  apply sum_nonneg; intro i _; split_ifs; rfl; exact hx i; rfl

lemma side_le_total {x : J → ℝ} (hx : ∀ i, 0 ≤ x i) (s : EpochSchedule.State J) :
    side x s ≤ total x := by
  apply sum_le_sum; intro i _; split_ifs; exact hx i; rfl; exact hx i

lemma mark_unchanged {x y : J → ℝ} {a b : K} {s : EpochSchedule.State J}
    (hr : ¬EpochSchedule.reset x y a b s) :
    dominant (EpochSchedule.update x y a b s)=dominant s := by
  simp only [EpochSchedule.update,ite_eq_right hr,dominant]

lemma side_variation {x y : J → ℝ} {s t : EpochSchedule.State J}
    (he : dominant s=dominant t) : |side x s-side y t| ≤ variation x y := by
  unfold side
  rw [←sum_sub_distrib]
  calc _ ≤ ∑ i, |(if dominant s=some i then 0 else if (dominant s).isSome then x i else 0)-
        (if dominant t=some i then 0 else if (dominant t).isSome then y i else 0)| := abs_sum_le_sum_abs _ _
       _ ≤ _ := by
        apply sum_le_sum
        intro i _
        rw [he]
        split_ifs <;> simp [abs_nonneg]

/-- Actual side totals and reset times are derived from the epoch recurrence. -/
def sideInput (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : ℝ := side (x t) (run x key t)
def epochReset (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) : Prop :=
  EpochSchedule.reset (x t) (x (t+1)) (key t) (key (t+1)) (run x key t)

lemma side_stepVariation (x : ℕ → J → ℝ) (key : ℕ → K) (t : ℕ) :
    stepVariation (sideInput x key) (epochReset x key) t ≤ variation (x (t+1)) (x t) := by
  unfold stepVariation
  split_ifs with hr
  · exact variation_nonneg _ _
  · apply side_variation
    exact mark_unchanged hr

/-- Side-reference refreshes are paid independently of the number of epochs. -/
lemma side_budget {δ : ℝ} (hδ : 0 < δ) (x : ℕ → J → ℝ)
    (key : ℕ → K) (hx : ∀ t i, 0 ≤ x t i) (N : ℕ) :
    (∑ t ∈ range N, charge δ (sideInput x key) (epochReset x key) t) ≤
      C δ*(∑ t ∈ range N, variation (x (t+1)) (x t)) := by
  exact (budget hδ _ _ (fun t => side_nonneg (hx t) _) N).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun t _ => side_stepVariation x key t) (C_nonneg hδ))

end KServer.CoarseSide

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseParameters

lemma regular_log_comparison {x : ℝ} (hx : (50/43:ℝ) ≤ x) :
    (1/20:ℝ)*(1+Real.log x) ≤ Real.log ((81/100:ℝ)*x+2/11) := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < (81/100:ℝ)*x+2/11 := by positivity
  have hs : x ≤ ((81/100:ℝ)*x+2/11)^2 := by nlinarith [sq_nonneg (x-50/43)]
  have hl := Real.log_le_log hx0 hs
  rw [Real.log_pow] at hl
  have hl₀ : (7/50:ℝ) ≤ Real.log x := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < (50/43:ℝ) by norm_num)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) hx)
  nlinarith

lemma dominant_log_comparison {u m : ℝ} (hu : 0 ≤ u) (huu : u ≤ 1/4)
    (hm : 1+u/2 ≤ m) : u/3 ≤ Real.log m := by
  have hpos : 0 < 1+u/2 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hi : (1+u/2)⁻¹ ≤ 1-u/3 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    nlinarith
  have hl := Real.log_le_log hpos hm
  linarith

variable {J : Type} [Fintype J]

/-- Quantitative size-ratio estimate from the genuine superadditive parent
size, without discarding the child's own true size. -/
lemma size_ratio {M a : J → ℝ} {V : ℝ} (hM : ∀ i, 0 ≤ M i)
    (_ : ∀ i, 0 ≤ a i) (hupper : ∀ i, a i ≤ (11/10)*M i)
    (hV : (∑ i,M i) ≤ V) (i : J) (hMi : 0 < M i) (hai : 0 < a i)
    (hlower : (9/10)*M i ≤ a i) :
    1+(9/11)*((∑ j,a j)/a i-1) ≤ V/M i := by
  classical
  have hs : (∑ j,a j)-a i ≤ (11/10)*(V-M i) := by
    have h := sum_le_sum (s:=univ.erase i) (f:=a) (g:=fun j => (11/10:ℝ)*M j) (fun j _ => hupper j)
    rw [←mul_sum,sum_erase_eq_sub (mem_univ i),sum_erase_eq_sub (mem_univ i)] at h
    nlinarith
  have hVm : M i ≤ V := (single_le_sum (fun j _ => hM j) (mem_univ i)).trans hV
  have hx := mul_le_mul_of_nonneg_right hlower (sub_nonneg.mpr hVm)
  apply (le_div_iff₀ hMi).mpr
  apply (mul_le_mul_iff_left₀ hai).mp
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hs hMi.le]

lemma regular_gap {M a : J → ℝ} {V A : ℝ} (hM : ∀ i, 0 ≤ M i)
    (ha : ∀ i, 0 ≤ a i) (hupper : ∀ i, a i ≤ (11/10)*M i)
    (hV : (∑ i,M i) ≤ V) (i : J) (hMi : 0 < M i) (hai : 0 < a i)
    (hlower : (9/10)*M i ≤ a i) (hA : (99/100)*A ≤ ∑ j,a j)
    (hreg : a i ≤ (86/100)*A) :
    (1/20:ℝ)*(1+Real.log (A/a i)) ≤ Real.log (V/M i) := by
  have hx : (50/43:ℝ) ≤ A/a i := (le_div_iff₀ hai).mpr (by linarith)
  have hr := size_ratio hM ha hupper hV i hMi hai hlower
  have hm : (81/100:ℝ)*(A/a i)+2/11 ≤ V/M i := by
    have h := div_le_div_of_nonneg_right hA hai.le
    rw [mul_div_assoc] at h
    nlinarith
  exact (regular_log_comparison hx).trans (Real.log_le_log (by positivity) hm)

lemma dominant_gap {M a : J → ℝ} {V A U : ℝ} (hM : ∀ i, 0 ≤ M i)
    (ha : ∀ i, 0 ≤ a i) (hupper : ∀ i, a i ≤ (11/10)*M i)
    (hV : (∑ i,M i) ≤ V) (i : J) (hMi : 0 < M i) (hai : 0 < a i)
    (hlower : (9/10)*M i ≤ a i) (hA : 0 < A) (haA : a i ≤ (101/100)*A)
    (hU : 0 ≤ U) (hUs : U ≤ (1001/1000)*((∑ j,a j)-a i))
    (hUu : U/A ≤ 1/4) :
    (1/20:ℝ)*(U/A) ≤ Real.log (V/M i) := by
  have hu : 0 ≤ U/A := div_nonneg hU hA.le
  have hr := size_ratio hM ha hupper hV i hMi hai hlower
  have hs : 0 ≤ (∑ j,a j)-a i := sub_nonneg.mpr (single_le_sum (fun j _ => ha j) (mem_univ i))
  have hb : U*a i ≤ (18/11)*A*((∑ j,a j)-a i) := by
    have h₁ := mul_le_mul_of_nonneg_right hUs hai.le
    have h₂ := mul_le_mul_of_nonneg_left haA hs
    nlinarith
  have hratio : U/A/2 ≤ (9/11)*((∑ j,a j)/a i-1) := by
    apply (mul_le_mul_iff_right₀ hA).mp
    apply (mul_le_mul_iff_right₀ hai).mp
    field_simp
    nlinarith
  have hl := dominant_log_comparison hu hUu (by linarith : 1+(U/A)/2 ≤ V/M i)
  linarith

/-- Literal true and held beta parameters. Their coefficient is chosen only
once; these functions do not depend on the horizon or posterior law. -/
def beta (k c cb ell M : ℝ) : ℝ := 3+cb/ell*Real.log (k/max M c)
def lowerSize (c δ H : ℝ) : ℝ := max c (H/(1+δ)^2)
def upperBeta (k c cb ell δ H : ℝ) : ℝ := 3+cb/ell*Real.log (k/lowerSize c δ H)

lemma beta_difference {k c cb ell M V : ℝ} (hk : 0 < k) (hc : 0 < c) (hM : c ≤ M) (hMV : M ≤ V) :
    beta k c cb ell M-beta k c cb ell V=cb/ell*Real.log (V/M) := by
  have hM0 : 0 < M := hc.trans_le hM
  have hV0 : 0 < V := hM0.trans_le hMV
  simp only [beta,max_eq_left hM,max_eq_left (hM.trans hMV)]
  rw [Real.log_div hk.ne' hM0.ne',Real.log_div hk.ne' hV0.ne',Real.log_div hV0.ne' hM0.ne']
  ring

lemma lowerSize_accuracy {c δ X H : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hX : c ≤ X)
    (_ : 0 ≤ H) (hlo : X ≤ (1+δ)^2*H) (hhi : H ≤ (1+δ)^2*X) :
    0 < lowerSize c δ H ∧ lowerSize c δ H ≤ X ∧ X ≤ (1+δ)^4*lowerSize c δ H := by
  have he : 0 < 1+δ := by linarith
  have he2 : 0 < (1+δ)^2 := sq_pos_of_pos he
  have hlow : H/(1+δ)^2 ≤ X := (div_le_iff₀ he2).mpr (by nlinarith)
  have hmax : H/(1+δ)^2 ≤ lowerSize c δ H := le_max_right _ _
  have hm : H ≤ (1+δ)^2*lowerSize c δ H := by
    have h := (div_le_iff₀ he2).mp hmax
    nlinarith
  refine ⟨hc.trans_le (le_max_left _ _),max_le hX hlow,?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hm he2.le]

lemma beta_upper_error {k c cb ell δ X H : ℝ} (hk : 0 < k) (hc : 0 < c)
    (hcb : 0 ≤ cb) (hell : 0 < ell) (hδ : 0 < δ) (hX : c ≤ X)
    (hH : 0 ≤ H) (hlo : X ≤ (1+δ)^2*H) (hhi : H ≤ (1+δ)^2*X) :
    beta k c cb ell X ≤ upperBeta k c cb ell δ H ∧
      upperBeta k c cb ell δ H ≤ beta k c cb ell X+4*cb*δ/ell := by
  have h := lowerSize_accuracy hc hδ hX hH hlo hhi
  have hX0 : 0 < X := hc.trans_le hX
  have hfac : 0 ≤ cb/ell := div_nonneg hcb hell.le
  have he : 0 < 1+δ := by linarith
  have hlog : 0 ≤ Real.log (X/lowerSize c δ H) ∧ Real.log (X/lowerSize c δ H) ≤ 4*δ := by
    constructor
    · apply Real.log_nonneg
      exact (one_le_div h.1).mpr h.2.1
    · have hb : X/lowerSize c δ H ≤ (1+δ)^4 := (div_le_iff₀ h.1).mpr (by nlinarith [h.2.2])
      have hl := Real.log_le_log (div_pos hX0 h.1) hb
      rw [Real.log_pow] at hl
      have hh := Real.log_le_sub_one_of_pos he
      nlinarith
  have hd : upperBeta k c cb ell δ H-beta k c cb ell X=cb/ell*Real.log (X/lowerSize c δ H) := by
    simp only [beta,upperBeta,max_eq_left hX]
    rw [Real.log_div hk.ne' h.1.ne',Real.log_div hk.ne' hX0.ne',Real.log_div hX0.ne' h.1.ne']
    ring
  constructor
  · nlinarith [mul_nonneg hfac hlog.1]
  · have hh := mul_le_mul_of_nonneg_left hlog.2 hfac
    have heq : cb/ell*(4*δ)=4*cb*δ/ell := by ring
    rw [heq] at hh
    linarith

end KServer.CoarseParameters

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.CoarseScale
open RankTracking RankFunctions CoreFlags
variable {Ω J R : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

lemma size_antitone : Antitone sizeRank := by
  apply antitone_of_hasDerivAt_nonpos sizeRank_derivative
  intro p
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_max_right _ _)

lemma rank_size {z p : ℝ} (hz : z ∈ Set.Icc 0 (1/100:ℝ)) (hp : 0 ≤ p) :
    rank z p ≤ 36*sizeRank p := by
  by_cases hs : p ≤ sstar
  · have h := size_antitone hs
    have he : sizeRank sstar=1/36 := by norm_num [sizeRank,sstar]
    rw [he] at h
    linarith [(rank_range hz hp).2]
  · rw [rank_cutoff z (le_of_not_ge hs)]
    exact mul_nonneg (by norm_num) (sizeRank_nonneg p)

def noncore (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a, if flag (P a) t ω then 0 else FineCaps.estimate δ 0 (P a) t ω

lemma noncore_nonneg (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    0 ≤ noncore δ P t ω := by
  apply sum_nonneg
  intro a _
  split_ifs
  · rfl
  · exact (FineCaps.estimate_range (by norm_num) (P a) t ω).1

lemma noncore_bound {δ : ℝ} (hδ : 0 < δ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    noncore δ P t ω ≤ 36*(1+δ)*CoarseProcess.size P t ω := by
  calc _ ≤ ∑ a, FineCaps.estimate δ 0 (P a) t ω := by
        apply sum_le_sum
        intro a _
        split_ifs
        · exact (FineCaps.estimate_range (by norm_num) (P a) t ω).1
        · rfl
       _ ≤ ∑ a, (1+δ)*(36*sizeRank ((P a).p t ω)) := by
        apply sum_le_sum
        intro a _
        exact (FineCaps.estimate_accuracy hδ (by norm_num) (P a) t ω).2.trans
          (mul_le_mul_of_nonneg_left (rank_size (by norm_num) ((P a).range t ω).1) (by linarith))
       _ = _ := by unfold CoarseProcess.size; rw [←mul_sum,←mul_sum]; ring

lemma term_variation {e e' : ℝ} (he : e ∈ Set.Icc 0 1) (he' : e' ∈ Set.Icc 0 1)
    (b b' : Bool) :
    |(if b' then 0 else e')-(if b then 0 else e)| ≤ |e'-e|+(if b'=b then (0:ℝ) else 1) := by
  cases b <;> cases b' <;> simp [abs_of_nonneg he.1,abs_of_nonneg he'.1] <;>
    linarith [he.2,he'.2,abs_nonneg (e'-e)]

lemma noncore_variation (δ : ℝ) (P : R → FilteredRanks w) (t : ℕ) (ω : Ω) :
    |noncore δ P (t+1) ω-noncore δ P t ω| ≤
      (∑ a, |FineCaps.estimate δ 0 (P a) (t+1) ω-FineCaps.estimate δ 0 (P a) t ω|)+
      ∑ a,change (P a) t ω := by
  unfold noncore
  rw [←sum_sub_distrib,←sum_add_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ =>
    term_variation (FineCaps.estimate_range (by norm_num) (P a) t ω)
      (FineCaps.estimate_range (by norm_num) (P a) (t+1) ω) _ _)

lemma mark_positive {x : J → ℝ} {s : EpochSchedule.State J} {o : J}
    (hs : EpochSchedule.Valid x s) (ho : EpochSchedule.dominant s=some o) : 0 < x o := by
  have hp : 0 < EpochSchedule.total s.reference := by
    unfold EpochSchedule.dominant at ho
    split_ifs at ho with h
    exact h.choose_spec.1
  have := EpochSchedule.dominant_large hs ho
  linarith

def scale (δ : ℝ) (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (s : EpochSchedule.State J) : ℝ :=
  (EpochSchedule.dominant s).elim 0 (fun i => noncore δ (P i) t ω)

lemma scale_nonneg (δ : ℝ) (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω)
    (s : EpochSchedule.State J) : 0 ≤ scale δ P t ω s := by
  unfold scale
  cases EpochSchedule.dominant s with
  | none => rfl
  | some i => exact noncore_nonneg δ (P i) t ω

lemma scale_bound {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : J → R → FilteredRanks w) (t : ℕ) (ω : Ω) (s : EpochSchedule.State J)
    (hs : EpochSchedule.Valid (CoarseEpoch.vector c δ P ω t) s) :
    scale δ P t ω s ≤ 41*EpochSchedule.total (CoarseEpoch.vector c δ P ω t) := by
  classical
  unfold scale
  cases ho : EpochSchedule.dominant s with
  | none => exact mul_nonneg (by norm_num) (EpochSchedule.total_nonneg (CoarseEpoch.vector_nonneg c δ P ω t))
  | some i =>
    have hp := mark_positive hs ho
    have ha : (CoarseProcess.active c δ (P i) ω t).active=true := by
      cases he : (CoarseProcess.active c δ (P i) ω t).active with
      | true => rfl
      | false =>
        have hz := (CoarseProcess.active_valid c δ (P i) ω t).2 he
        change 0 < (CoarseProcess.active c δ (P i) ω t).value at hp
        linarith
    have hlo := ((CoarseProcess.active_accuracy hc hδ hδu (P i) ω t).1 ha).1
    have hv := single_le_sum (fun j _ => CoarseEpoch.vector_nonneg c δ P ω t j) (mem_univ i)
    change (CoarseProcess.active c δ (P i) ω t).value ≤ EpochSchedule.total (CoarseEpoch.vector c δ P ω t) at hv
    have hb := noncore_bound hδ (P i) t ω
    have hm := CoarseProcess.size_nonneg (P i) t ω
    have hd := mul_le_mul_of_nonneg_right hδu hm
    change noncore δ (P i) t ω ≤ _
    nlinarith

lemma scale_unchanged_variation (δ : ℝ) (P : J → R → FilteredRanks w)
    (t : ℕ) (ω : Ω) (s s' : EpochSchedule.State J)
    (he : EpochSchedule.dominant s'=EpochSchedule.dominant s) :
    |scale δ P (t+1) ω s'-scale δ P t ω s| ≤
      ∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω) := by
  have hnonneg i : 0 ≤ (∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
      ∑ a,change (P i a) t ω := by
    apply add_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
    apply sum_nonneg; intro a _; unfold change; split_ifs <;> norm_num
  unfold scale
  rw [he]
  cases ho : EpochSchedule.dominant s with
  | none => simpa using sum_nonneg (fun i _ => hnonneg i)
  | some i => exact (noncore_variation δ (P i) t ω).trans (single_le_sum (fun i _ => hnonneg i) (mem_univ i))

end KServer.CoarseScale

namespace KServer.CoarseScale
open RankTracking RankFunctions CoreFlags
variable {Ω J R K : Type} [Fintype Ω] [Fintype J] [Fintype R] {w : Ω → ℝ}

lemma scale_step {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (P : J → R → FilteredRanks w) (ω : Ω) (key : ℕ → K) (t : ℕ) :
    let x := CoarseEpoch.vector c δ P ω
    let s := EpochSchedule.run x key
    |scale δ P (t+1) ω (s (t+1))-scale δ P t ω (s t)| ≤
      (∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω))+
      41*EpochSchedule.wholesale (x t) (x (t+1)) (key t) (key (t+1)) (s t) := by
  intro x s
  have hv n := EpochSchedule.run_valid x key (CoarseEpoch.vector_nonneg c δ P ω) n
  by_cases hr : EpochSchedule.reset (x t) (x (t+1)) (key t) (key (t+1)) (s t)
  · have hb₀ := scale_bound hc hδ hδu P t ω (s t) (hv t)
    have hb₁ := scale_bound hc hδ hδu P (t+1) ω (s (t+1)) (hv (t+1))
    have hn₀ := scale_nonneg δ P t ω (s t)
    have hn₁ := scale_nonneg δ P (t+1) ω (s (t+1))
    have hj : 0 ≤ ∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω) := by
      apply sum_nonneg
      intro i _
      apply add_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
      apply sum_nonneg; intro a _; unfold change; split_ifs <;> norm_num
    rw [EpochSchedule.wholesale,ite_eq_left hr]
    apply abs_le.mpr
    constructor <;> linarith
  · rw [EpochSchedule.wholesale,ite_eq_right hr,mul_zero,add_zero]
    apply scale_unchanged_variation
    exact CoarseSide.mark_unchanged hr

/-- The change of dominant flex scale is paid by actual elementary trackers,
core flips, and wholesale totals. This includes changes of dominant identity. -/
lemma scale_budget {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδu : δ ≤ 1/1000)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω,w ω=1)
    (P : J → R → FilteredRanks w) (key : Ω → ℕ → K) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω =>
      |scale δ P (t+1) ω (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) (t+1))-
       scale δ P t ω (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t)|)) ≤
      (80/δ+(CoreFlags.tolerance^2)⁻¹)*
        ((∑ i, ∑ a, ∑ t ∈ range N, avg w (fun ω => |(P i a).p (t+1) ω-(P i a).before (t+1) ω|))+
          Fintype.card J*Fintype.card R)+
      41*(∑ t ∈ range N, avg w (fun ω => EpochSchedule.wholesale
        (CoarseEpoch.vector c δ P ω t) (CoarseEpoch.vector c δ P ω (t+1))
        (key ω t) (key ω (t+1)) (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t))) := by
  let drift i a := ∑ t ∈ range N, avg w (fun ω => |(P i a).p (t+1) ω-(P i a).before (t+1) ω|)
  have he i a := FineCaps.estimate_variation_budget hw hw1 hδ (by linarith) (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) (P i a) N
  have hf := CoreFlags.core_change_budget hw hw1 (fun ia : J × R => P ia.1 ia.2) N
  have hest : (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,
      |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)) ≤
      (80/δ)*((∑ i,∑ a,drift i a)+Fintype.card J*Fintype.card R) := by
    simp_rw [avg_sum]
    rw [sum_comm]
    calc _ = ∑ i, ∑ a, ∑ t ∈ range N, avg w (fun ω =>
        |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|) := by
          apply sum_congr rfl; intro i _; exact sum_comm
         _ ≤ ∑ i,∑ a,(80/δ)*(drift i a+1) := sum_le_sum fun i _ => sum_le_sum fun a _ => he i a
         _ = _ := by simp_rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,card_univ]
  have hflags : (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,change (P i a) t ω)) ≤
      (CoreFlags.tolerance^2)⁻¹*((∑ i,∑ a,drift i a)+Fintype.card J*Fintype.card R) := by
    have hd : (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,
        |(P i a).p (t+1) ω-(P i a).before (t+1) ω|)) = ∑ i,∑ a,drift i a := by
      simp_rw [avg_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      exact sum_comm
    simpa only [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,hd] using hf
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω =>
        (∑ i, ((∑ a, |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|)+
        ∑ a,change (P i a) t ω))+
        41*EpochSchedule.wholesale (CoarseEpoch.vector c δ P ω t) (CoarseEpoch.vector c δ P ω (t+1))
          (key ω t) (key ω (t+1)) (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t)) := by
        exact sum_le_sum fun t _ => avg_mono hw (fun ω => scale_step hc hδ hδu P ω (key ω) t)
       _ = (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,
          |FineCaps.estimate δ 0 (P i a) (t+1) ω-FineCaps.estimate δ 0 (P i a) t ω|))+
         (∑ t ∈ range N, avg w (fun ω => ∑ i,∑ a,change (P i a) t ω))+
         41*(∑ t ∈ range N, avg w (fun ω => EpochSchedule.wholesale
           (CoarseEpoch.vector c δ P ω t) (CoarseEpoch.vector c δ P ω (t+1))
           (key ω t) (key ω (t+1)) (EpochSchedule.run (CoarseEpoch.vector c δ P ω) (key ω) t))) := by
          simp_rw [sum_add_distrib,avg_add,avg_mul,sum_add_distrib,←mul_sum]
       _ ≤ _ := by dsimp only [drift] at hest hflags; nlinarith

end KServer.CoarseScale

end

end OAI
