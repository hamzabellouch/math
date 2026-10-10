import Mathlib
import OAI.Combinatorics.KServer.Ranks

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.RankTracking
variable {Ω : Type*} [Fintype Ω]
/-- Reference reset policy run on every input step. -/
def held (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, ω => p 0 ω
  | t+1, ω => if test (p (t+1) ω) (held test p t ω) then p (t+1) ω else held test p t ω

omit [Fintype Ω] in
lemma held_range (test : ℝ → ℝ → Prop) [DecidableRel test] {p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω ∈ Set.Icc 0 1) : ∀ t ω, held test p t ω ∈ Set.Icc 0 1 := by
  intro t
  induction t with
  | zero => exact hp 0
  | succ t ih => intro ω; dsimp [held]; split_ifs <;> [exact hp _ _; exact ih ω]

lemma held_adapted (test : ℝ → ℝ → Prop) [DecidableRel test] {w : Ω → ℝ}
    (R : FilteredRanks w) : ∀ t, Adapted (R.history t) (held test R.p t) := by
  intro t
  induction t with
  | zero => exact R.adapted 0
  | succ t ih =>
    intro ω ω' hh
    have hprev := ih ω ω' (R.refines t ω ω' hh)
    have hnow := R.adapted (t+1) ω ω' hh
    simp only [held,hnow,hprev]

/-- Exact bounded affine potential used in the manuscript. -/
def potential (p r : ℝ) : ℝ := p*(1-p)+(p-r)^2
lemma potential_affine (p r : ℝ) : potential p r=(1-2*r)*p+r^2 := by unfold potential; ring
lemma potential_bounds {p r : ℝ} (hp : p ∈ Set.Icc 0 1) (hr : r ∈ Set.Icc 0 1) :
    potential p r ∈ Set.Icc 0 1 := by
  constructor
  · exact add_nonneg (mul_nonneg hp.1 (sub_nonneg.mpr hp.2)) (sq_nonneg _)
  · rw [potential_affine]
    have hpr := mul_nonneg hp.1 (mul_nonneg hr.1 (sub_nonneg.mpr hr.2))
    have hqr := mul_nonneg (sub_nonneg.mpr hp.2) (mul_nonneg hr.1 (sub_nonneg.mpr hr.2))
    have ha := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hr.2)
    have hb := mul_nonneg hp.1 hr.1
    nlinarith
lemma slope_abs {r : ℝ} (hr : r ∈ Set.Icc 0 1) : |1-2*r| ≤1 := by
  rw [abs_le]; constructor <;> linarith [hr.1,hr.2]

def credit (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if test (p (t+1) ω) (held test p t ω) then (p (t+1) ω-held test p t ω)^2 else 0

omit [Fintype Ω] in
lemma credit_step (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ)
    (before : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    credit test p t ω = potential (p t ω) (held test p t ω) -
      potential (p (t+1) ω) (held test p (t+1) ω) +
      (1-2*held test p t ω)*(before (t+1) ω-p t ω) +
      (1-2*held test p t ω)*(p (t+1) ω-before (t+1) ω) := by
  simp only [credit,held]
  split_ifs <;> simp only [potential] <;> ring

lemma expected_credit_step (test : ℝ → ℝ → Prop) [DecidableRel test]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (R : FilteredRanks w) (t : ℕ) :
    avg w (credit test R.p t) ≤
      avg w (fun ω => potential (R.p t ω) (held test R.p t ω)) -
      avg w (fun ω => potential (R.p (t+1) ω) (held test R.p (t+1) ω)) +
      avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|) := by
  have hf : Adapted (R.history t) (fun ω => 1-2*held test R.p t ω) := by
    intro ω ω' hh; dsimp only; rw [held_adapted test R t ω ω' hh]
  calc _ = avg w (fun ω => potential (R.p t ω) (held test R.p t ω) -
      potential (R.p (t+1) ω) (held test R.p (t+1) ω) +
      (1-2*held test R.p t ω)*(R.before (t+1) ω-R.p t ω) +
      (1-2*held test R.p t ω)*(R.p (t+1) ω-R.before (t+1) ω)) := by
        congr 1; funext ω; exact credit_step _ _ _ _ _
       _ = _ + avg w (fun ω => (1-2*held test R.p t ω)*(R.p (t+1) ω-R.before (t+1) ω)) := by
        rw [avg_add,avg_add,avg_sub,filtering_affine R t _ hf,add_zero]
       _ ≤ _ := by
        apply add_le_add_right
        apply avg_mono hw
        intro ω
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right (slope_abs (held_range test R.range t ω)) (abs_nonneg _)).trans_eq (one_mul _))

/-- Signed filtering is retained at every step, before the reset decision. -/
theorem reset_credit_bound (test : ℝ → ℝ → Prop) [DecidableRel test]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (R : FilteredRanks w) (N : ℕ) :
    (∑ t ∈ Finset.range N, avg w (credit test R.p t)) ≤
      (∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1 := by
  let V : ℕ → ℝ := fun t => avg w (fun ω => potential (R.p t ω) (held test R.p t ω))
  have hV t : 0 ≤ V t ∧ V t ≤1 := by
    constructor
    · have hh := avg_mono hw (fun ω => (potential_bounds (R.range t ω) (held_range test R.range t ω)).1)
      simpa only [avg_const w hw1 0] using hh
    · have hh := avg_mono hw (fun ω => (potential_bounds (R.range t ω) (held_range test R.range t ω)).2)
      simpa only [avg_const w hw1 1] using hh
  have hs : (∑ t ∈ Finset.range N, avg w (credit test R.p t)) ≤
      V 0-V N+(∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|)) := by
    calc _ ≤ ∑ t ∈ Finset.range N, (V t-V (t+1)+avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|)) :=
          sum_le_sum fun t _ => expected_credit_step test hw R t
         _ = _ := by rw [sum_add_distrib,Finset.sum_range_sub']
  linarith [(hV 0).2,(hV N).1]


/-- Source's scalar factor-loss constant, including zero endpoints. -/
lemma sqrt_factor_gap_one {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξh : ξ < 1/2) (hfail : (1+ξ)*b ≤ a) :
    (ξ/5)*(a-b) ≤ (Real.sqrt a-Real.sqrt b)^2 := by
  let A := Real.sqrt a
  let B := Real.sqrt b
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAs : A^2=a := Real.sq_sqrt ha
  have hBs : B^2=b := Real.sq_sqrt hb
  have hba : b ≤ a := by nlinarith [mul_nonneg hξ.le hb]
  have hAB : B ≤ A := Real.sqrt_le_sqrt hba
  have hlin : ξ*(A+B) ≤ 5*(A-B) := by
    by_cases hz : A+B=0
    · rw [hz]; linarith
    have hsum : 0 < A+B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hz)
    by_contra hbad
    have hd : A-B < (ξ/5)*(A+B) := by linarith
    have hprod : ξ*(A+B) ≤ (1/2)*(A+B) := mul_le_mul_of_nonneg_right hξh.le hsum.le
    have hbS : (9/20)*(A+B) ≤ B := by linarith
    have hbSq : (81/400)*(A+B)^2 ≤ B^2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ B-(9/20)*(A+B))
        (by positivity : 0 ≤ B+(9/20)*(A+B))]
    have hmul := mul_le_mul_of_nonneg_left hbSq hξ.le
    have hmul' := mul_lt_mul_of_pos_right hd hsum
    have hpos := mul_pos hξ (sq_pos_of_pos hsum)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlin (sub_nonneg.mpr hAB)
  change (ξ/5)*(a-b) ≤ (A-B)^2
  nlinarith

lemma sqrt_factor_gap {a b ξ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hξ : 0 < ξ) (hξh : ξ < 1/2)
    (hfail : (1+ξ)*a < b ∨ (1+ξ)*b < a) :
    (ξ/5)*|a-b| ≤ (Real.sqrt a-Real.sqrt b)^2 := by
  rcases hfail with hab | hba
  · have hle : a ≤ b := by nlinarith [mul_nonneg hξ.le ha]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hh := sqrt_factor_gap_one hb ha hξ hξh hab.le
    nlinarith
  · have hle : b ≤ a := by nlinarith [mul_nonneg hξ.le hb]
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact sqrt_factor_gap_one ha hb hξ hξh hba.le

def factorTest (f : ℝ → ℝ) (ξ p r : ℝ) : Prop :=
  (1+ξ)*f p < f r ∨ (1+ξ)*f r < f p

instance (f : ℝ → ℝ) (ξ : ℝ) : DecidableRel (factorTest f ξ) := Classical.decRel _

omit [Fintype Ω] in
lemma factor_held_accurate (f : ℝ → ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (hf : ∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ f p) {p : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p t ω ∈ Set.Icc 0 1) (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*f (p t ω) ≤ f (held (factorTest f ξ) p t ω) ∧
      f (held (factorTest f ξ) p t ω) ≤ (1+ξ)*f (p t ω) := by
  have hself (x : ℝ) (hx : 0 ≤ x) : (1+ξ)⁻¹*x ≤ x ∧ x ≤ (1+ξ)*x := by
    constructor
    · rw [inv_mul_le_iff₀ (by linarith : 0<1+ξ)]
      nlinarith [mul_nonneg hξ.le hx]
    · nlinarith [mul_nonneg hξ.le hx]
  cases t with
  | zero => exact hself _ (hf _ (hp 0 ω))
  | succ t =>
    simp only [held]
    split_ifs with ht
    · exact hself _ (hf _ (hp _ _))
    · rw [factorTest,not_or,not_lt,not_lt] at ht
      constructor
      · rw [inv_mul_le_iff₀ (by linarith : 0<1+ξ)]
        exact ht.2
      · exact ht.1

omit [Fintype Ω] in
lemma factor_movement_credit (f : ℝ → ℝ) {ξ K : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2)
    (hK : 0 ≤ K) (hf : ∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ f p)
    (hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ r ∈ Set.Icc (0:ℝ) 1,
      |Real.sqrt (f p)-Real.sqrt (f r)| ≤ K*|p-r|)
    {p : ℕ → Ω → ℝ} (hp : ∀ t ω, p t ω ∈ Set.Icc 0 1) (t : ℕ) (ω : Ω) :
    |f (held (factorTest f ξ) p (t+1) ω)-f (held (factorTest f ξ) p t ω)| ≤
      (5*K^2/ξ)*credit (factorTest f ξ) p t ω := by
  have hr := held_range (factorTest f ξ) hp t ω
  by_cases ht : factorTest f ξ (p (t+1) ω) (held (factorTest f ξ) p t ω)
  · simp only [held,ite_eq_left ht,credit]
    have hg := sqrt_factor_gap (hf (p (t+1) ω) (hp (t+1) ω)) (hf _ hr) hξ hξh ht
    have hl := hlip (p (t+1) ω) (hp (t+1) ω) _ hr
    have hs : (Real.sqrt (f (p (t+1) ω))-Real.sqrt (f (held (factorTest f ξ) p t ω)))^2 ≤
        K^2*(p (t+1) ω-held (factorTest f ξ) p t ω)^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))).mpr hl
      simpa only [sq_abs,mul_pow] using hh
    have hmove : ξ*|f (p (t+1) ω)-f (held (factorTest f ξ) p t ω)| ≤
        5*K^2*(p (t+1) ω-held (factorTest f ξ) p t ω)^2 := by nlinarith [hg.trans hs]
    calc _ = (ξ*|f (p (t+1) ω)-f (held (factorTest f ξ) p t ω)|)/ξ := by field_simp
         _ ≤ (5*K^2*(p (t+1) ω-held (factorTest f ξ) p t ω)^2)/ξ :=
          div_le_div_of_nonneg_right hmove hξ.le
         _ = _ := by ring
  · simp [held,ht,credit]

/-- Actual causal multiplicative held estimates, with horizon-independent
additive initialization allowance and the source's C/xi drift dependence. -/
theorem multiplicative_rank_tracking {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω=1) (R : FilteredRanks w) (f : ℝ → ℝ) {ξ K : ℝ}
    (hξ : 0 < ξ) (hξh : ξ < 1/2) (hK : 0 ≤ K)
    (hf : ∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ f p)
    (hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ r ∈ Set.Icc (0:ℝ) 1,
      |Real.sqrt (f p)-Real.sqrt (f r)| ≤ K*|p-r|) :
    ∃ estimate : ℕ → Ω → ℝ,
      (∀ t, Adapted (R.history t) (estimate t)) ∧
      (∀ t ω, (1+ξ)⁻¹*f (R.p t ω) ≤ estimate t ω ∧ estimate t ω ≤ (1+ξ)*f (R.p t ω)) ∧
      ∀ N, (∑ t ∈ Finset.range N, avg w (fun ω => |estimate (t+1) ω-estimate t ω|)) ≤
        (5*K^2/ξ)*((∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1) := by
  let estimate := fun t ω => f (held (factorTest f ξ) R.p t ω)
  refine ⟨estimate,?_,?_,?_⟩
  · intro t ω ω' hh
    dsimp [estimate]
    rw [held_adapted (factorTest f ξ) R t ω ω' hh]
  · intro t ω; exact factor_held_accurate f hξ hf R.range t ω
  · intro N
    calc _ ≤ ∑ t ∈ Finset.range N, avg w (fun ω => (5*K^2/ξ)*credit (factorTest f ξ) R.p t ω) :=
          sum_le_sum fun t _ => avg_mono hw (factor_movement_credit f hξ hξh hK hf hlip R.range t)
         _ = (5*K^2/ξ)*(∑ t ∈ Finset.range N, avg w (credit (factorTest f ξ) R.p t)) := by
          simp_rw [avg_mul]; rw [mul_sum]
         _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (factorTest f ξ) hw hw1 R N) (by positivity)


def absoluteTest (δ p r : ℝ) : Prop := δ < |p-r|
instance (δ : ℝ) : DecidableRel (absoluteTest δ) := Classical.decRel _

def resetIndicator (test : ℝ → ℝ → Prop) [DecidableRel test] (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  if test (p (t+1) ω) (held test p t ω) then 1 else 0

/-- The absolute tracker used for all core flags. Its cost is the actual
number of reference refreshes, not the variation of the raw posteriors. -/
theorem absolute_rank_tracking {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω=1) (R : FilteredRanks w) {δ : ℝ} (hδ : 0 < δ) :
    (∀ t ω, |R.p t ω-held (absoluteTest δ) R.p t ω| ≤ δ) ∧
    ∀ N, (∑ t ∈ Finset.range N, avg w (resetIndicator (absoluteTest δ) R.p t)) ≤
      (δ^2)⁻¹*((∑ t ∈ Finset.range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1) := by
  constructor
  · intro t ω
    cases t with
    | zero => simp [held,hδ.le]
    | succ t =>
      simp only [held]
      split_ifs with ht
      · simp [hδ.le]
      · exact le_of_not_gt ht
  · intro N
    have hstep (t : ℕ) (ω : Ω) : resetIndicator (absoluteTest δ) R.p t ω ≤
        (δ^2)⁻¹*credit (absoluteTest δ) R.p t ω := by
      simp only [resetIndicator,credit]
      split_ifs with ht
      · have hsq : δ^2 ≤ (R.p (t+1) ω-held (absoluteTest δ) R.p t ω)^2 := by
          have habs : δ ≤ |R.p (t+1) ω-held (absoluteTest δ) R.p t ω| := le_of_lt ht
          simpa only [sq_abs] using (sq_le_sq₀ hδ.le (abs_nonneg _)).mpr habs
        rw [le_inv_mul_iff₀ (sq_pos_of_pos hδ),mul_one]
        exact hsq
      · simp
    calc _ ≤ ∑ t ∈ Finset.range N, avg w (fun ω => (δ^2)⁻¹*credit (absoluteTest δ) R.p t ω) :=
          sum_le_sum fun t _ => avg_mono hw (hstep t)
         _ = (δ^2)⁻¹*(∑ t ∈ Finset.range N, avg w (credit (absoluteTest δ) R.p t)) := by
          simp_rw [avg_mul]; rw [mul_sum]
         _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (absoluteTest δ) hw hw1 R N) (by positivity)

omit [Fintype Ω] in
/-- Causal hold-or-reset rules never increase total scalar input variation.
The deviation from the held reference pays for any waiting interval. -/
lemma held_variation_step (test : ℝ → ℝ → Prop) [DecidableRel test]
    (p : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    |held test p (t+1) ω-held test p t ω|+|p (t+1) ω-held test p (t+1) ω| ≤
      |p (t+1) ω-p t ω|+|p t ω-held test p t ω| := by
  have hh := abs_sub_le (p (t+1) ω) (p t ω) (held test p t ω)
  simp only [held]
  split_ifs <;> simpa using hh

omit [Fintype Ω] in
theorem held_variation (test : ℝ → ℝ → Prop) [DecidableRel test]
    (p : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    (∑ t ∈ Finset.range N, |held test p (t+1) ω-held test p t ω|) ≤
      ∑ t ∈ Finset.range N, |p (t+1) ω-p t ω| := by
  have hstrong : (∑ t ∈ Finset.range N, |held test p (t+1) ω-held test p t ω|)+
      |p N ω-held test p N ω| ≤ ∑ t ∈ Finset.range N, |p (t+1) ω-p t ω| := by
    induction N with
    | zero => simp [held]
    | succ N ih =>
      simp only [sum_range_succ]
      linarith [held_variation_step test p N ω]
  linarith [abs_nonneg (p N ω-held test p N ω)]

lemma factor_change_charge {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
    (ht : (1+δ)*a < b ∨ (1+δ)*b < a) : a+b ≤ (1+2/δ)*|a-b| := by
  rcases ht with hab | hba
  · have hab' : a ≤ b := by nlinarith [mul_nonneg hδ.le ha]
    rw [abs_of_nonpos (sub_nonpos.mpr hab')]
    calc a+b = (δ*(a+b))/δ := by field_simp
         _ ≤ ((δ+2)*(b-a))/δ := div_le_div_of_nonneg_right (by nlinarith) hδ.le
         _ = (1+2/δ)*-(a-b) := by field_simp; ring
  · have hba' : b ≤ a := by nlinarith [mul_nonneg hδ.le hb]
    rw [abs_of_nonneg (sub_nonneg.mpr hba')]
    calc a+b = (δ*(a+b))/δ := by field_simp
         _ ≤ ((δ+2)*(a-b))/δ := div_le_div_of_nonneg_right (by nlinarith) hδ.le
         _ = (1+2/δ)*(a-b) := by field_simp

end KServer.RankTracking
namespace KServer.CoreFlags
open KServer.RankTracking
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

/-- §03: the literal absolute reference tolerance p*/8, p*=1/24. -/
def tolerance : ℝ := (1/24)/8
lemma tolerance_pos : 0 < tolerance := by norm_num [tolerance]
def flag (R : FilteredRanks w) (t : ℕ) (ω : Ω) : Bool :=
  decide (held (absoluteTest tolerance) R.p t ω ≤ (1/24 : ℝ)/2)

def change (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  if flag R (t+1) ω = flag R t ω then 0 else 1

lemma flag_accuracy (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |R.p t ω - held (absoluteTest tolerance) R.p t ω| ≤ tolerance := by
  cases t with
  | zero => simp [held,tolerance_pos.le]
  | succ t =>
    simp only [held]
    split_ifs with ht
    · simp [tolerance_pos.le]
    · exact le_of_not_gt ht

lemma core_upper (R : FilteredRanks w) {t : ℕ} {ω : Ω} (hf : flag R t ω = true) :
    R.p t ω ≤ 5*(1/24 : ℝ)/8 := by
  have hh : held (absoluteTest tolerance) R.p t ω ≤ (1/24 : ℝ)/2 := by simpa [flag] using hf
  have ha := (abs_le.mp (flag_accuracy R t ω)).2
  norm_num [tolerance] at *
  linarith

lemma noncore_lower (R : FilteredRanks w) {t : ℕ} {ω : Ω} (hf : flag R t ω = false) :
    3*(1/24 : ℝ)/8 < R.p t ω := by
  have hh : (1/24 : ℝ)/2 < held (absoluteTest tolerance) R.p t ω := by
    simpa [flag,not_le] using hf
  have ha := (abs_le.mp (flag_accuracy R t ω)).1
  norm_num [tolerance] at *
  linarith

lemma small_is_core (R : FilteredRanks w) {t : ℕ} {ω : Ω} (hp : R.p t ω < (1/24 : ℝ)/4) :
    flag R t ω = true := by
  cases hf : flag R t ω with
  | true => rfl
  | false => have := noncore_lower R hf; norm_num at *; linarith

lemma change_le_reset (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    change R t ω ≤ resetIndicator (absoluteTest tolerance) R.p t ω := by
  by_cases ht : absoluteTest tolerance (R.p (t+1) ω) (held (absoluteTest tolerance) R.p t ω)
  · simp only [resetIndicator,ite_eq_left ht,change]
    split_ifs <;> norm_num
  · have he : flag R (t+1) ω = flag R t ω := by simp [flag,held,ht]
    simp [change,he,resetIndicator,ht]

/-- The exact number of changed flags is charged to the fixed absolute trackers.
No raw posterior total variation is charged. -/
theorem core_change_budget {J : Type} [Fintype J]
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1) (R : J → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => ∑ j, change (R j) t ω)) ≤
      (tolerance^2)⁻¹ * ((∑ t ∈ range N, avg w
        (fun ω => ∑ j, |(R j).p (t+1) ω-(R j).before (t+1) ω|)) + Fintype.card J) := by
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => ∑ j, resetIndicator (absoluteTest tolerance) (R j).p t ω) := by
        apply sum_le_sum
        intro t _
        apply avg_mono hw
        intro ω
        apply sum_le_sum
        intro j _
        exact change_le_reset (R j) t ω
    _ = ∑ j, ∑ t ∈ range N, avg w (resetIndicator (absoluteTest tolerance) (R j).p t) := by
      simp_rw [avg_sum]; rw [sum_comm]
    _ ≤ ∑ j, (tolerance^2)⁻¹ * ((∑ t ∈ range N, avg w
        (fun ω => |(R j).p (t+1) ω-(R j).before (t+1) ω|))+1) := by
      exact sum_le_sum fun j _ => (absolute_rank_tracking hw hw1 (R j) tolerance_pos).2 N
    _ = _ := by
      rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
      congr 2
      simp_rw [avg_sum]
      exact sum_comm

lemma flag_adapted (R : FilteredRanks w) (t : ℕ) {ω z : Ω}
    (he : R.history t ω = R.history t z) : flag R t ω=flag R t z := by
  unfold flag
  rw [held_adapted (absoluteTest tolerance) R t ω z he]

/-- Changing core flags after inspecting new posteriors costs at most one per
changed flag, since each rank remains in [0,1]. -/
lemma flagged_mass_change {J : Type} [Fintype J] (p : J → ℝ)
    (hp : ∀ j, p j ∈ Set.Icc 0 1) (K K' : J → Bool) :
    |(∑ j, if K' j then p j else 0) - (∑ j, if K j then p j else 0)| ≤
      ∑ j, if K' j = K j then (0:ℝ) else 1 := by
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j _
  have hh := hp j
  cases K j <;> cases K' j <;> simp [abs_of_nonneg hh.1,hh.2]

end KServer.CoreFlags
end


/- Rank functions for dominated allocation, as in §03, equation explicit-rank. -/


noncomputable section
open Set Filter
namespace KServer.RankFunctions

def pstar : ℝ := 1 / 24
def sstar : ℝ := 5 / 8

def A (z : ℝ) : ℝ := 18 / 7 - z * (102 / 49)
def B (z : ℝ) : ℝ := z * (1152 / 343)
def middle (z p : ℝ) : ℝ :=
  A z * (sstar - p) ^ 2 + B z * (sstar - p) ^ 3

def rank (z p : ℝ) : ℝ :=
  if p ≤ pstar then 1 - (3 + z) * p
  else if p ≤ sstar then middle z p else 0

def slope (z p : ℝ) : ℝ :=
  if p ≤ pstar then -(3 + z)
  else if p ≤ sstar then -2 * A z * (sstar - p) - 3 * B z * (sstar - p) ^ 2 else 0

lemma middle_literal (z p : ℝ) :
    middle z p = (sstar - p) ^ 2 *
      (18 / 7 - z * (6 / 49 + 1152 / 343 * (p - pstar))) := by
  unfold middle A B sstar pstar
  ring

/-- C¹ gluing at a scalar threshold, applied twice to the rank formula. -/
lemma derivative_ite_le {f g f' g' : ℝ → ℝ} {c : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (he : f c = g c) (hd : f' c = g' c) (x : ℝ) :
    HasDerivAt (fun p => if p ≤ c then f p else g p)
      (if x ≤ c then f' x else g' x) x := by
  rcases lt_trichotomy x c with hx | hx | hx
  · rw [ite_eq_left hx.le]
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with p hp
    exact ite_eq_left hp.le
  · subst x
    rw [ite_eq_left le_rfl]
    have hleft : HasDerivWithinAt (fun p => if p ≤ c then f p else g p)
        (f' c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr
      · intro p hp
        exact ite_eq_left hp
      · exact ite_eq_left le_rfl
    have hright : HasDerivWithinAt (fun p => if p ≤ c then f p else g p)
        (f' c) (Ici c) c := by
      rw [hd]
      apply (hg c).hasDerivWithinAt.congr
      · intro p hp
        by_cases ht : p ≤ c
        · have : p = c := le_antisymm ht hp
          subst p
          simpa using he
        · exact ite_eq_right ht
      · simpa using he
    have h := hleft.union hright
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using h
  · rw [ite_eq_right hx.not_ge]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with p hp
    exact ite_eq_right hp.not_ge

lemma middle_derivative (z p : ℝ) :
    HasDerivAt (middle z) (-2 * A z * (sstar - p) - 3 * B z * (sstar - p) ^ 2) p := by
  have h := (((hasDerivAt_id p).const_sub sstar).pow 2).const_mul (A z)
  have h' := (((hasDerivAt_id p).const_sub sstar).pow 3).const_mul (B z)
  convert h.add h' using 1
  all_goals first | rfl | (norm_num [id_eq]; ring)

lemma rank_derivative (z p : ℝ) : HasDerivAt (rank z) (slope z p) p := by
  have hcut (x : ℝ) : HasDerivAt (fun p => if p ≤ sstar then middle z p else 0)
      (if x ≤ sstar then -2 * A z * (sstar - x) - 3 * B z * (sstar - x) ^ 2 else 0) x := by
    apply derivative_ite_le (middle_derivative z) (fun x => hasDerivAt_const x 0)
    · simp [middle]
    · simp
  apply derivative_ite_le (f' := fun _ => -(3 + z))
    (fun x => by simpa using ((hasDerivAt_id x).const_mul (3 + z)).const_sub 1)
    hcut
  · norm_num [pstar, sstar, middle, A, B]
    ring
  · norm_num [pstar, sstar, A, B]
    ring

lemma coefficients {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    2 ≤ A z ∧ 0 ≤ B z := by
  dsimp [A, B]
  constructor <;> nlinarith [hz.1, hz.2]

lemma middle_slope_monotone {z x y : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ))
    (hxy : x ≤ y) (hys : y ≤ sstar) :
    -2 * A z * (sstar - x) - 3 * B z * (sstar - x) ^ 2 ≤
      -2 * A z * (sstar - y) - 3 * B z * (sstar - y) ^ 2 := by
  obtain ⟨hA, hB⟩ := coefficients hz
  have hlin : A z * (sstar - y) ≤ A z * (sstar - x) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hsq : (sstar - y) ^ 2 ≤ (sstar - x) ^ 2 := by nlinarith
  have hquad := mul_le_mul_of_nonneg_left hsq hB
  nlinarith

lemma slope_monotone {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    Monotone (slope z) := by
  have hps : pstar ≤ sstar := by norm_num [pstar, sstar]
  have hmatch : -2 * A z * (sstar - pstar) - 3 * B z * (sstar - pstar) ^ 2 = -(3 + z) := by
    unfold A B sstar pstar
    ring
  intro x y hxy
  by_cases hx : x ≤ pstar
  · by_cases hy : y ≤ pstar
    · simp [slope, hx, hy]
    · by_cases hys : y ≤ sstar
      · simp only [slope, ite_eq_left hx, ite_eq_right hy, ite_eq_left hys]
        rw [← hmatch]
        exact middle_slope_monotone hz (le_of_not_ge hy) hys
      · simp only [slope, ite_eq_left hx, ite_eq_right hy, ite_eq_right hys]
        linarith [hz.1]
  · have hy : ¬ y ≤ pstar := by linarith
    by_cases hys : y ≤ sstar
    · have hxs : x ≤ sstar := hxy.trans hys
      simp only [slope, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxs, ite_eq_left hys]
      exact middle_slope_monotone hz hxy hys
    · by_cases hxs : x ≤ sstar
      · simp only [slope, ite_eq_right hx, ite_eq_right hy, ite_eq_left hxs, ite_eq_right hys]
        have h := middle_slope_monotone hz hxs (le_refl sstar)
        simpa using h
      · simp [slope, hx, hy, hxs, hys]

lemma rank_convex {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    ConvexOn ℝ univ (rank z) := by
  apply Monotone.convexOn_univ_of_deriv (fun p => (rank_derivative z p).differentiableAt)
  have he : deriv (rank z) = slope z := funext fun p => (rank_derivative z p).deriv
  rw [he]
  exact slope_monotone hz

lemma rank_antitone {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    Antitone (rank z) := by
  apply antitone_of_hasDerivAt_nonpos (rank_derivative z)
  intro p
  dsimp only [Pi.zero_apply]
  have hps : pstar < sstar := by norm_num [pstar, sstar]
  have hzero : slope z sstar = 0 := by simp [slope, not_le.mpr hps]
  by_cases hp : p ≤ sstar
  · exact (slope_monotone hz hp).trans_eq hzero
  · have hpp : ¬p ≤ pstar := by linarith
    simp [slope, hpp, hp]

lemma rank_zero (z : ℝ) : rank z 0 = 1 := by norm_num [rank, pstar]

lemma rank_cutoff (z : ℝ) {p : ℝ} (hp : sstar ≤ p) : rank z p = 0 := by
  have hpp : ¬ p ≤ pstar := by norm_num [sstar, pstar] at *; linarith
  simp only [rank, ite_eq_right hpp]
  split_ifs with h
  · have : p = sstar := le_antisymm h hp
    simp [this, middle]
  · rfl

lemma rank_pos {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (hp : p < sstar) :
    0 < rank z p := by
  by_cases h : p ≤ pstar
  · rw [rank, ite_eq_left h]
    have hmul := mul_le_mul_of_nonneg_left h (by linarith [hz.1] : 0 ≤ 3 + z)
    norm_num [pstar] at hmul
    nlinarith [hz.2]
  · rw [rank, ite_eq_right h, ite_eq_left hp.le]
    obtain ⟨hA, hB⟩ := coefficients hz
    have hx : 0 < sstar - p := sub_pos.mpr hp
    have h2 : 0 < A z * (sstar - p)^2 := mul_pos (by linarith) (sq_pos_of_pos hx)
    have h3 : 0 ≤ B z * (sstar - p)^3 := mul_nonneg hB (pow_nonneg hx.le _)
    dsimp [middle]
    linarith

lemma rank_nonneg {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (p : ℝ) :
    0 ≤ rank z p := by
  by_cases hp : p < sstar
  · exact (rank_pos hz hp).le
  · rw [rank_cutoff z (le_of_not_gt hp)]

lemma rank_range {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (hp : 0 ≤ p) :
    rank z p ∈ Set.Icc 0 1 := by
  exact ⟨rank_nonneg hz p, (rank_antitone hz hp).trans_eq (rank_zero z)⟩

/-- Minus the derivative in beta, exactly as defined after eq:explicit-rank. -/
def parameterSlope (p : ℝ) : ℝ :=
  if p ≤ pstar then p else if p ≤ sstar then
    (sstar - p)^2 * (6 / 49 + 1152 / 343 * (p - pstar)) else 0

lemma rank_parameter_affine (z p : ℝ) :
    rank z p = rank 0 p - z * parameterSlope p := by
  dsimp [rank, parameterSlope]
  split_ifs <;> simp [middle, A, B, sstar, pstar] <;> ring

lemma parameterSlope_nonneg {p : ℝ} (hp : 0 ≤ p) : 0 ≤ parameterSlope p := by
  dsimp [parameterSlope]
  split_ifs with h h'
  · exact hp
  · have : 0 ≤ 6 / 49 + 1152 / 343 * (p - pstar) := by linarith
    exact mul_nonneg (sq_nonneg _) this
  · rfl

lemma rank_parameter_antitone {p : ℝ} (hp : 0 ≤ p) :
    Antitone (fun z => rank z p) := by
  intro x y hxy
  change rank y p ≤ rank x p
  rw [rank_parameter_affine x, rank_parameter_affine y]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hxy (parameterSlope_nonneg hp)) _

lemma parameterSlope_compare {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ))
    (hp : pstar / 4 ≤ p) :
    rank z p / 96 ≤ parameterSlope p ∧ parameterSlope p ≤ rank z p := by
  by_cases h : p ≤ pstar
  · simp only [rank, parameterSlope, ite_eq_left h]
    norm_num [pstar] at h hp
    have hzp : 0 ≤ z * p := mul_nonneg hz.1 (by linarith)
    have hmul := mul_le_mul_of_nonneg_left h (by linarith [hz.1] : 0 ≤ 3 + z)
    constructor <;> nlinarith [hz.2]
  · by_cases h' : p ≤ sstar
    · simp only [rank, parameterSlope, ite_eq_right h, ite_eq_left h', middle_literal]
      let c : ℝ := 6 / 49 + 1152 / 343 * (p - pstar)
      have hc0 : 6 / 49 ≤ c := by dsimp [c]; linarith
      have hc1 : c ≤ 102 / 49 := by dsimp [c]; norm_num [pstar, sstar] at *; linarith
      have hzc0 : 0 ≤ z * c := mul_nonneg hz.1 (by linarith)
      have hzc1 : z * c ≤ (1 / 100) * (102 / 49) :=
        mul_le_mul hz.2 hc1 (by linarith) (by norm_num)
      have hlo : (18 / 7 - z * c) / 96 ≤ c := by linarith
      have hhi : c ≤ 18 / 7 - z * c := by linarith
      constructor
      · have hh := mul_le_mul_of_nonneg_left hlo (sq_nonneg (sstar - p))
        change (sstar - p)^2 * (18 / 7 - z*c) / 96 ≤ (sstar - p)^2 * c
        nlinarith [hh]
      · exact mul_le_mul_of_nonneg_left hhi (sq_nonneg _)
    · simp [rank, parameterSlope, h, h']

lemma sqrt_slope_bound {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ))
    (hp0 : 0 ≤ p) (hp : p < sstar) :
    ‖slope z p / (2 * Real.sqrt (rank z p))‖ ≤ 4 := by
  have hr := rank_pos hz hp
  have hs := Real.sqrt_pos.mpr hr
  have hsq := Real.sq_sqrt hr.le
  have hsign : slope z p ≤ 0 := by
    have hh := slope_monotone hz hp.le
    have hps : ¬ sstar ≤ pstar := by norm_num [sstar, pstar]
    simpa [slope, hps] using hh
  rw [Real.norm_eq_abs, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hsign (by positivity))]
  rw [← neg_div, div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (rank z p))]
  by_cases h : p ≤ pstar
  · have hrsmall : 4 / 5 ≤ rank z p := by
      rw [rank, ite_eq_left h]
      have ht := mul_le_mul_of_nonneg_left h (by linarith [hz.1] : 0 ≤ 3 + z)
      norm_num [pstar] at ht
      nlinarith [hz.2]
    have hslo : 1 / 2 ≤ Real.sqrt (rank z p) := by nlinarith
    simp only [slope, ite_eq_left h]
    linarith [hz.2]
  · have hx : 0 < sstar - p := sub_pos.mpr hp
    have hx1 : sstar - p ≤ 1 := by norm_num [sstar]; linarith
    have hA : 2 ≤ A z := (coefficients hz).1
    have hA' : A z ≤ 3 := by dsimp [A]; linarith [hz.1]
    have hB : 0 ≤ B z := (coefficients hz).2
    have hB' : B z ≤ 1 / 10 := by dsimp [B]; linarith [hz.2]
    have hrank : rank z p = (sstar - p)^2 * (A z + B z * (sstar - p)) := by
      rw [rank, ite_eq_right h, ite_eq_left hp.le]
      dsimp [middle]
      ring
    have hBx := mul_le_mul_of_nonneg_left hx1 hB
    have hBx0 := mul_nonneg hB hx.le
    have hslo : sstar - p ≤ Real.sqrt (rank z p) := by
      have hh := mul_le_mul_of_nonneg_left (by linarith : 1 ≤ A z + B z * (sstar - p)) (sq_nonneg (sstar - p))
      rw [← hrank] at hh
      nlinarith
    simp only [slope, ite_eq_right h, ite_eq_left hp.le]
    have hh := mul_le_mul_of_nonneg_left (by linarith : 2 * A z + 3 * (B z * (sstar - p)) ≤ 8) hx.le
    nlinarith

lemma sqrt_right_derivative {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    HasDerivWithinAt (fun p => Real.sqrt (rank z p))
      (if p < sstar then slope z p / (2 * Real.sqrt (rank z p)) else 0) (Ici p) p := by
  by_cases hp : p < sstar
  · rw [ite_eq_left hp]
    exact ((rank_derivative z p).sqrt (ne_of_gt (rank_pos hz hp))).hasDerivWithinAt
  · rw [ite_eq_right hp]
    apply (hasDerivWithinAt_const p (Ici p) (0 : ℝ)).congr
    · intro x hx
      rw [rank_cutoff z ((le_of_not_gt hp).trans hx), Real.sqrt_zero]
    · rw [rank_cutoff z (le_of_not_gt hp), Real.sqrt_zero]

lemma sqrt_rank_lipschitz {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    LipschitzOnWith 4 (fun p => Real.sqrt (rank z p)) (Ici 0) := by
  have hc : Continuous (fun p => Real.sqrt (rank z p)) :=
    Real.continuous_sqrt.comp (continuous_iff_continuousAt.mpr fun p => (rank_derivative z p).continuousAt)
  have hbound (p : ℝ) (hp : 0 ≤ p) :
      ‖if p < sstar then slope z p / (2 * Real.sqrt (rank z p)) else 0‖ ≤ 4 := by
    split_ifs with h
    · exact sqrt_slope_bound hz hp h
    · norm_num
  have hsegment (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      ‖Real.sqrt (rank z b) - Real.sqrt (rank z a)‖ ≤ 4 * (b - a) := by
    exact norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn
      (fun p _ => sqrt_right_derivative hz) (fun p hp => hbound p (ha.trans hp.1)) b ⟨hab, le_rfl⟩
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  rcases le_total x y with h | h
  · simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := hsegment x y hx h
    rw [norm_sub_rev] at hh
    convert hh using 1
    norm_num
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h), NNReal.coe_ofNat] using hsegment y x hy h


/-- The broader size function, literally as in §03. -/
def sizeRank (p : ℝ) : ℝ := (max (3 / 4 - p) 0)^2 / (3 / 4)^2

lemma sizeRank_piece (p : ℝ) :
    sizeRank p = if p ≤ 3 / 4 then (3 / 4 - p)^2 / (3 / 4)^2 else 0 := by
  by_cases h : p ≤ 3 / 4
  · simp [sizeRank, h]
  · simp [sizeRank, h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

lemma sizeRank_derivative (p : ℝ) :
    HasDerivAt sizeRank (-(32 / 9) * max (3 / 4 - p) 0) p := by
  have hf (x : ℝ) : HasDerivAt (fun p : ℝ => (3 / 4 - p)^2 / (3 / 4)^2)
      (-(32 / 9) * (3 / 4 - x)) x := by
    convert (((hasDerivAt_id x).const_sub (3 / 4)).pow 2).div_const ((3 / 4)^2) using 1
    all_goals first | rfl | (norm_num [id_eq]; ring)
  have ht := derivative_ite_le hf (fun x => hasDerivAt_const x (0 : ℝ))
    (c := 3 / 4) (by norm_num) (by norm_num) p
  convert ht using 1
  · exact funext sizeRank_piece
  · by_cases h : p ≤ 3 / 4
    · simp [h]
    · simp [h, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]

lemma sizeRank_convex : ConvexOn ℝ univ sizeRank := by
  apply Monotone.convexOn_univ_of_deriv (fun p => (sizeRank_derivative p).differentiableAt)
  intro x y hxy
  rw [(sizeRank_derivative x).deriv, (sizeRank_derivative y).deriv]
  exact mul_le_mul_of_nonpos_left (max_le_max (by linarith) le_rfl) (by norm_num)

lemma sizeRank_zero : sizeRank 0 = 1 := by norm_num [sizeRank]
lemma sizeRank_one : sizeRank 1 = 0 := by norm_num [sizeRank]
lemma sizeRank_nonneg (p : ℝ) : 0 ≤ sizeRank p := div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma sizeRank_le_complement {p : ℝ} (hp : p ∈ Set.Icc 0 1) : sizeRank p ≤ 1 - p := by
  rw [sizeRank_piece]
  split_ifs with h
  · norm_num
    have hm := mul_nonneg hp.1 (sub_nonneg.mpr h)
    nlinarith
  · linarith [hp.2]

lemma sqrt_sizeRank (p : ℝ) : Real.sqrt (sizeRank p) = (4 / 3) * max (3 / 4 - p) 0 := by
  rw [sizeRank, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (le_max_right _ _)]
  norm_num
  ring

lemma sqrt_sizeRank_lipschitz : LipschitzWith (4 / 3) (fun p => Real.sqrt (sizeRank p)) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [sqrt_sizeRank, Real.norm_eq_abs]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have h := abs_max_sub_max_le_abs (3 / 4 - x) (3 / 4 - y) (0 : ℝ)
  have he : |(3 / 4 - x) - (3 / 4 - y)| = |x-y| := by
    rw [show (3 / 4 - x) - (3 / 4 - y) = -(x-y) by ring, abs_neg]
  rw [he] at h
  exact mul_le_mul_of_nonneg_left h (by norm_num)

end KServer.RankFunctions

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FineCaps
open KServer.RankTracking KServer.RankFunctions KServer.CoreFlags
variable {Ω : Type} [Fintype Ω] {w : Ω → ℝ}

def estimate (ξ z : ℝ) (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  rank z (held (factorTest (rank z) ξ) R.p t ω)

lemma estimate_range {ξ z : ℝ} (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : estimate ξ z R t ω ∈ Set.Icc 0 1 :=
  rank_range hz (held_range (factorTest (rank z) ξ) R.range t ω).1

lemma estimate_accuracy {ξ z : ℝ} (hξ : 0 < ξ) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    (1+ξ)⁻¹*rank z (R.p t ω) ≤ estimate ξ z R t ω ∧
      estimate ξ z R t ω ≤ (1+ξ)*rank z (R.p t ω) :=
  factor_held_accurate (rank z) hξ (fun _ hp => (rank_range hz hp.1).1) R.range t ω

lemma relative_absolute {ξ f E : ℝ} (hξ : 0 ≤ ξ) (hf : 0 ≤ f)
    (hl : (1+ξ)⁻¹*f ≤ E) (hu : E ≤ (1+ξ)*f) : |E-f| ≤ ξ*f := by
  have hx : 0 < 1+ξ := by linarith
  have hh := mul_le_mul_of_nonneg_left hl hx.le
  have he : (1+ξ)*((1+ξ)⁻¹*f)=f := by rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hx),one_mul]
  rw [he] at hh
  apply abs_le.mpr
  constructor
  · by_cases hEf : E ≤ f
    · have := mul_le_mul_of_nonneg_left hEf hξ
      nlinarith
    · have := mul_nonneg hξ hf
      linarith
  · nlinarith

lemma estimate_absolute {ξ z : ℝ} (hξ : 0 < ξ) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |estimate ξ z R t ω-rank z (R.p t ω)| ≤ ξ*rank z (R.p t ω) :=
  relative_absolute hξ.le (rank_range hz (R.range t ω).1).1
    (estimate_accuracy hξ hz R t ω).1 (estimate_accuracy hξ hz R t ω).2

lemma interpolate_rank (a p : ℝ) :
    (1-a)*rank 0 p+a*rank (1/100) p = rank (a/100) p := by
  rw [rank_parameter_affine (1/100),rank_parameter_affine (a/100)]
  ring

def interpolated (ξ a : ℝ) (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  (1-a)*estimate ξ 0 R t ω+a*estimate ξ (1/100) R t ω

lemma interpolated_range {ξ a : ℝ} (ha : a ∈ Set.Icc 0 1)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : interpolated ξ a R t ω ∈ Set.Icc 0 1 := by
  have h0 := estimate_range (ξ := ξ) (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have h1 := estimate_range (ξ := ξ) (by norm_num : (1/100:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have hA : 0 ≤ 1-a := by linarith [ha.2]
  have l0 := mul_nonneg hA h0.1
  have l1 := mul_nonneg ha.1 h1.1
  have u0 := mul_le_mul_of_nonneg_left h0.2 hA
  have u1 := mul_le_mul_of_nonneg_left h1.2 ha.1
  constructor <;> dsimp [interpolated] <;> nlinarith

lemma interpolated_accuracy {ξ a : ℝ} (hξ : 0 < ξ) (ha : a ∈ Set.Icc 0 1)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |interpolated ξ a R t ω-rank (a/100) (R.p t ω)| ≤ ξ*rank (a/100) (R.p t ω) := by
  have h0 := estimate_absolute hξ (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have h1 := estimate_absolute hξ (by norm_num : (1/100:ℝ) ∈ Set.Icc 0 (1/100)) R t ω
  have hA : 0 ≤ 1-a := by linarith [ha.2]
  rw [←interpolate_rank]
  calc |interpolated ξ a R t ω-((1-a)*rank 0 (R.p t ω)+a*rank (1/100) (R.p t ω))| =
      |(1-a)*(estimate ξ 0 R t ω-rank 0 (R.p t ω)) +
        a*(estimate ξ (1/100) R t ω-rank (1/100) (R.p t ω))| := by
          unfold interpolated; congr 1; ring
    _ ≤ |(1-a)*(estimate ξ 0 R t ω-rank 0 (R.p t ω))| +
        |a*(estimate ξ (1/100) R t ω-rank (1/100) (R.p t ω))| := abs_add_le _ _
    _ = (1-a)*|estimate ξ 0 R t ω-rank 0 (R.p t ω)| +
        a*|estimate ξ (1/100) R t ω-rank (1/100) (R.p t ω)| := by
          rw [abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg ha.1]
    _ ≤ (1-a)*(ξ*rank 0 (R.p t ω))+a*(ξ*rank (1/100) (R.p t ω)) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hA) (mul_le_mul_of_nonneg_left h1 ha.1)
    _ = _ := by ring

/-- §03 flex-estimate error, including exact zero at the common cutoff. -/
lemma noncore_interpolation_error {ξ a z ε : ℝ} (hξ : 0 < ξ) (ha : a ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 (1/100 : ℝ)) (hza : z ≤ a/100) (hea : a/100-z ≤ ε)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) (hf : flag R t ω=false) :
    |interpolated ξ a R t ω-rank z (R.p t ω)| ≤ (ξ+ε)*rank z (R.p t ω) := by
  have hp : pstar/4 ≤ R.p t ω := by
    have := noncore_lower R hf
    norm_num [pstar] at *
    linarith
  have hg := parameterSlope_compare hz hp
  have hg0 := parameterSlope_nonneg (R.range t ω).1
  have hm := rank_parameter_antitone (R.range t ω).1 hza
  have hre : rank z (R.p t ω)-rank (a/100) (R.p t ω) =
      (a/100-z)*parameterSlope (R.p t ω) := by
    rw [rank_parameter_affine z,rank_parameter_affine (a/100)]; ring
  have hs : |rank (a/100) (R.p t ω)-rank z (R.p t ω)| ≤ ε*rank z (R.p t ω) := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hm),hre]
    exact (mul_le_mul_of_nonneg_left hg.2 (sub_nonneg.mpr hza)).trans
      (mul_le_mul_of_nonneg_right hea (rank_range hz (R.range t ω).1).1)
  calc _ ≤ |interpolated ξ a R t ω-rank (a/100) (R.p t ω)| +
       |rank (a/100) (R.p t ω)-rank z (R.p t ω)| := abs_sub_le _ _ _
    _ ≤ ξ*rank (a/100) (R.p t ω)+ε*rank z (R.p t ω) :=
      add_le_add (interpolated_accuracy hξ ha R t ω) hs
    _ ≤ ξ*rank z (R.p t ω)+ε*rank z (R.p t ω) :=
      add_le_add (mul_le_mul_of_nonneg_left hm hξ.le) (le_refl _)
    _ = _ := by ring

/-- Deterministic scaling of an accurately tracked flex term. Parameters here
are already normalized by ell: l=lambda_b/ell, e=error/ell,
g=gamma/ell, b=epsilon_b/ell. All zero-flex cases are included. -/
lemma cap_scaling {F E Fc l e g b : ℝ}
    (hF : 0 ≤ F) (hE : |E-F| ≤ e*F) (he : 0 ≤ e)
    (hl : 0 < l) (hls : l ≤ 1/4) (hel : e ≤ l/4)
    (hg : 4*l ≤ g) (hb : 4*l ≤ b) (hfc : Fc ≤ (1-g)*F) :
    (Fc ≤ (1-l)*E ∧ (1-l)*E ≤ F) ∧
    (F ≤ (1+l)*E ∧ (1+l)*E ≤ (1+b)*F) := by
  have hnear := abs_le.mp hE
  have hl1 : 0 ≤ 1-l := by linarith
  have hl2 : 0 ≤ 1+l := by linarith
  have low := mul_le_mul_of_nonneg_left hnear.1 hl1
  have up := mul_le_mul_of_nonneg_left hnear.2 hl1
  have low' := mul_le_mul_of_nonneg_left hnear.1 hl2
  have up' := mul_le_mul_of_nonneg_left hnear.2 hl2
  have hle : l*e ≤ e/4 := by nlinarith
  have hge : l+e ≤ g := by linarith
  have hbe : l+e+l*e ≤ b := by nlinarith
  have hpos : e+l*e ≤ l := by nlinarith
  have h01 := mul_le_mul_of_nonneg_right hge hF
  have h02 := mul_le_mul_of_nonneg_right hbe hF
  have h03 := mul_le_mul_of_nonneg_right hpos hF
  have h04 : e ≤ l := by linarith
  have h05 := mul_le_mul_of_nonneg_right h04 hF
  have h06 := mul_nonneg (mul_nonneg hl.le he) hF
  constructor <;> constructor <;> nlinarith

/-- The concrete endpoint tracker, not a separately postulated estimate. -/
lemma estimate_variation_budget (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    {ξ z : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => |estimate ξ z R (t+1) ω-estimate ξ z R t ω|)) ≤
      (80/ξ)*((∑ t ∈ range N, avg w (fun ω => |R.p (t+1) ω-R.before (t+1) ω|))+1) := by
  have hlip : ∀ p ∈ Set.Icc (0:ℝ) 1, ∀ r ∈ Set.Icc (0:ℝ) 1,
      |Real.sqrt (rank z p)-Real.sqrt (rank z r)| ≤ (4:ℝ)*|p-r| := by
    intro p hp r hr
    have hh := (lipschitzOnWith_iff_norm_sub_le.mp (sqrt_rank_lipschitz hz)) hp.1 hr.1
    simpa only [Real.norm_eq_abs, NNReal.coe_ofNat] using hh
  have hs t ω := factor_movement_credit (rank z) hξ hξh (show (0:ℝ) ≤ 4 by norm_num)
    (fun p hp => (rank_range hz hp.1).1) hlip R.range t ω
  have hs' t ω : |estimate ξ z R (t+1) ω-estimate ξ z R t ω| ≤
      (80/ξ)*credit (factorTest (rank z) ξ) R.p t ω := by
    simpa only [estimate, show (5:ℝ)*4^2=80 by norm_num] using hs t ω
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => (80/ξ)*credit (factorTest (rank z) ξ) R.p t ω) :=
        sum_le_sum fun t _ => avg_mono hw (hs' t)
    _ = (80/ξ)*(∑ t ∈ range N, avg w (credit (factorTest (rank z) ξ) R.p t)) := by
        simp_rw [avg_mul]; rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (reset_credit_bound (factorTest (rank z) ξ) hw hw1 R N)
        (by positivity)

lemma interpolated_variation {ξ a : ℝ} (ha : a ∈ Set.Icc 0 1)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |interpolated ξ a R (t+1) ω-interpolated ξ a R t ω| ≤
      |estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω|+
      |estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω| := by
  have hA : 0 ≤ 1-a := by linarith [ha.2]
  calc _ = |(1-a)*(estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω) +
        a*(estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω)| := by
          unfold interpolated; congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_mul,abs_mul,abs_of_nonneg hA,abs_of_nonneg ha.1]
      simpa only [one_mul] using add_le_add
        (mul_le_mul_of_nonneg_right (show 1-a ≤ 1 by linarith [ha.1])
          (abs_nonneg (estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω)))
        (mul_le_mul_of_nonneg_right ha.2
          (abs_nonneg (estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω))))

/-- One rank's core-plus-scaled-flex contribution to the actual cap. -/
def capTerm (ξ a κ : ℝ) (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  if flag R t ω then 1 else κ*interpolated ξ a R t ω

lemma capTerm_range {ξ a κ : ℝ} (ha : a ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 2)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : capTerm ξ a κ R t ω ∈ Set.Icc 0 2 := by
  have hh := interpolated_range (ξ := ξ) ha R t ω
  dsimp [capTerm]
  split_ifs
  · constructor <;> norm_num
  · exact ⟨mul_nonneg hκ.1 hh.1, (mul_le_mul_of_nonneg_left hh.2 hκ.1).trans (by simpa using hκ.2)⟩

lemma capTerm_variation {ξ a κ : ℝ} (ha : a ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 2)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    |capTerm ξ a κ R (t+1) ω-capTerm ξ a κ R t ω| ≤
      2*(|estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω|+
        |estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω|+change R t ω) := by
  have hv := interpolated_variation (ξ := ξ) ha R t ω
  have hn0 := abs_nonneg (estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω)
  have hn1 := abs_nonneg (estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω)
  by_cases he : flag R (t+1) ω=flag R t ω
  · have hc : change R t ω=0 := by simp [change,he]
    rw [hc,add_zero]
    unfold capTerm
    rw [he]
    split_ifs
    · simp only [sub_self,abs_zero]; positivity
    · rw [←mul_sub,abs_mul,abs_of_nonneg hκ.1]
      exact (mul_le_mul_of_nonneg_left hv hκ.1).trans
        (mul_le_mul_of_nonneg_right hκ.2 (add_nonneg hn0 hn1))
  · have hc : change R t ω=1 := by simp [change,he]
    have h0 := capTerm_range (ξ := ξ) ha hκ R t ω
    have h1 := capTerm_range (ξ := ξ) ha hκ R (t+1) ω
    have hb : |capTerm ξ a κ R (t+1) ω-capTerm ξ a κ R t ω| ≤ 2 := by
      exact abs_le.mpr ⟨by linarith [h0.1,h0.2,h1.1,h1.2],by linarith [h0.1,h0.2,h1.1,h1.2]⟩
    rw [hc]
    linarith

/-- Fine changes can be selected pathwise; wholesale changes are excluded only
when the interpolation and scale parameters are actually held fixed. -/
def fineVariation (ξ : ℝ) (a κ : ℕ → Ω → ℝ) (wholesale : ℕ → Ω → Bool)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) : ℝ :=
  if wholesale t ω then 0 else
    |capTerm ξ (a (t+1) ω) (κ (t+1) ω) R (t+1) ω-capTerm ξ (a t ω) (κ t ω) R t ω|

lemma fineVariation_step {ξ : ℝ} (a κ : ℕ → Ω → ℝ) (wholesale : ℕ → Ω → Bool)
    (ha : ∀ t ω, a t ω ∈ Set.Icc 0 1) (hκ : ∀ t ω, κ t ω ∈ Set.Icc 0 2)
    (hhold : ∀ t ω, wholesale t ω=false → a (t+1) ω=a t ω ∧ κ (t+1) ω=κ t ω)
    (R : FilteredRanks w) (t : ℕ) (ω : Ω) :
    fineVariation ξ a κ wholesale R t ω ≤
      2*(|estimate ξ 0 R (t+1) ω-estimate ξ 0 R t ω|+
        |estimate ξ (1/100) R (t+1) ω-estimate ξ (1/100) R t ω|+change R t ω) := by
  cases h : wholesale t ω with
  | true =>
    simp only [fineVariation,h,↓reduceIte]
    have : 0 ≤ change R t ω := by unfold change; split_ifs <;> norm_num
    positivity
  | false =>
    obtain ⟨hA,hK⟩ := hhold t ω h
    simpa only [fineVariation,h,Bool.false_eq_true,↓reduceIte,hA,hK] using
      capTerm_variation (ξ := ξ) (ha t ω) (hκ t ω) R t ω

lemma all_endpoint_budget {J : Type} [Fintype J]
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    {ξ z : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2) (hz : z ∈ Set.Icc 0 (1/100 : ℝ))
    (R : J → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => ∑ j,
      |estimate ξ z (R j) (t+1) ω-estimate ξ z (R j) t ω|)) ≤
      (80/ξ)*((∑ t ∈ range N, avg w
        (fun ω => ∑ j, |(R j).p (t+1) ω-(R j).before (t+1) ω|))+Fintype.card J) := by
  calc _ = ∑ j, ∑ t ∈ range N, avg w
        (fun ω => |estimate ξ z (R j) (t+1) ω-estimate ξ z (R j) t ω|) := by
          simp_rw [avg_sum]; rw [sum_comm]
    _ ≤ ∑ j, (80/ξ)*((∑ t ∈ range N, avg w
        (fun ω => |(R j).p (t+1) ω-(R j).before (t+1) ω|))+1) :=
          sum_le_sum fun j _ => estimate_variation_budget hw hw1 hξ hξh hz (R j) N
    _ = _ := by
      rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
      congr 2
      simp_rw [avg_sum]
      exact sum_comm

/-- §03 fine-cap budget. The right side has one uniform initialization term
per rank, not one per coarse epoch. Arbitrary pathwise nonwholesale selection
is valid only after the all-step filtering credits have been accounted for. -/
theorem fine_cap_budget {J : Type} [Fintype J]
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω=1)
    {ξ : ℝ} (hξ : 0 < ξ) (hξh : ξ < 1/2)
    (a κ : J → ℕ → Ω → ℝ) (wholesale : J → ℕ → Ω → Bool)
    (ha : ∀ j t ω, a j t ω ∈ Set.Icc 0 1) (hκ : ∀ j t ω, κ j t ω ∈ Set.Icc 0 2)
    (hhold : ∀ j t ω, wholesale j t ω=false →
      a j (t+1) ω=a j t ω ∧ κ j (t+1) ω=κ j t ω)
    (R : J → FilteredRanks w) (N : ℕ) :
    (∑ t ∈ range N, avg w (fun ω => ∑ j, fineVariation ξ (a j) (κ j) (wholesale j) (R j) t ω)) ≤
      2*(160/ξ+(tolerance^2)⁻¹)*((∑ t ∈ range N, avg w
        (fun ω => ∑ j, |(R j).p (t+1) ω-(R j).before (t+1) ω|))+Fintype.card J) := by
  have h0 := all_endpoint_budget hw hw1 hξ hξh
    (by norm_num : (0:ℝ) ∈ Set.Icc 0 (1/100)) R N
  have h1 := all_endpoint_budget hw hw1 hξ hξh
    (by norm_num : (1/100:ℝ) ∈ Set.Icc 0 (1/100)) R N
  have hc := core_change_budget hw hw1 R N
  calc _ ≤ ∑ t ∈ range N, avg w (fun ω => ∑ j,
        2*(|estimate ξ 0 (R j) (t+1) ω-estimate ξ 0 (R j) t ω|+
          |estimate ξ (1/100) (R j) (t+1) ω-estimate ξ (1/100) (R j) t ω|+change (R j) t ω)) := by
        apply sum_le_sum
        intro t _
        apply avg_mono hw
        intro ω
        exact sum_le_sum fun j _ => fineVariation_step (a j) (κ j) (wholesale j)
          (ha j) (hκ j) (hhold j) (R j) t ω
    _ = 2*((∑ t ∈ range N, avg w (fun ω => ∑ j,
          |estimate ξ 0 (R j) (t+1) ω-estimate ξ 0 (R j) t ω|))+
        (∑ t ∈ range N, avg w (fun ω => ∑ j,
          |estimate ξ (1/100) (R j) (t+1) ω-estimate ξ (1/100) (R j) t ω|))+
        (∑ t ∈ range N, avg w (fun ω => ∑ j, change (R j) t ω))) := by
          simp_rw [←mul_sum,sum_add_distrib,avg_mul,avg_add]
          rw [←mul_sum,sum_add_distrib,sum_add_distrib]
    _ ≤ _ := by
      have h := add_le_add (add_le_add h0 h1) hc
      have h' := mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 2 by norm_num)
      convert h' using 1
      first | rfl | ring

end KServer.FineCaps
end

end

/- Finite-law rank superadditivity and summation by parts. -/


noncomputable section
open Finset
open scoped BigOperators
namespace KServer.RankOrder

lemma convex_tangent {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hd : ∀ x, DifferentiableAt ℝ f x) (x y : ℝ) :
    deriv f x * (y - x) ≤ f y - f x := by
  rcases lt_trichotomy x y with h | h | h
  · have hh := hf.le_slope_of_hasDerivAt (Set.mem_univ x) (Set.mem_univ y) h (hd x).hasDerivAt
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
  · subst y
    simp
  · have hh := hf.slope_le_of_hasDerivAt (Set.mem_univ y) (Set.mem_univ x) h (hd x).hasDerivAt
    rw [slope_def_field] at hh
    have ht := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

lemma convex_sum_of_prefix {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f)
    (hd : ∀ x, DifferentiableAt ℝ f x) {n : ℕ} {x y : ℕ → ℝ}
    (hmono : ∀ a b, a ≤ b → b < n → x a ≤ x b)
    (hprefix : ∀ m ≤ n, ∑ i ∈ range m, y i ≤ ∑ i ∈ range m, x i)
    (htotal : ∑ i ∈ range n, y i = ∑ i ∈ range n, x i) :
    ∑ i ∈ range n, f (x i) ≤ ∑ i ∈ range n, f (y i) := by
  have hD : ∀ m ≤ n, ∑ i ∈ range m, (y i - x i) ≤ 0 := by
    intro m hm
    rw [sum_sub_distrib]
    exact sub_nonpos.mpr (hprefix m hm)
  have hD0 : ∑ i ∈ range n, (y i - x i) = 0 := by
    rw [sum_sub_distrib, htotal, sub_self]
  have hmonod := hf.monotoneOn_deriv (fun x _ => hd x)
  have hnonneg : 0 ≤ ∑ i ∈ range n, deriv f (x i) * (y i - x i) := by
    have he := sum_range_by_parts (fun i => deriv f (x i)) (fun i => y i - x i) n
    simp only [smul_eq_mul, hD0, mul_zero, zero_sub] at he
    rw [he]
    apply neg_nonneg.mpr
    apply sum_nonpos
    intro i hi
    have hi' : i + 1 < n := by have := mem_range.mp hi; omega
    have hdif : 0 ≤ deriv f (x (i + 1)) - deriv f (x i) := by
      exact sub_nonneg.mpr (hmonod (Set.mem_univ _) (Set.mem_univ _) (hmono i (i + 1) (by omega) hi'))
    exact mul_nonpos_of_nonneg_of_nonpos hdif (hD (i + 1) hi'.le)
  have hsum := sum_le_sum (s := range n) (fun i _ => convex_tangent hf hd (x i) (y i))
  rw [sum_sub_distrib] at hsum
  linarith

def extend {n : ℕ} (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then v ⟨i, hi⟩ else 0

lemma extend_fin {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : extend v i = v i := by
  simp [extend, i.isLt]

lemma sum_outside {ι : Type*} [DecidableEq ι] (S B : Finset ι) :
    (∑ i ∈ S, if i ∈ B then (0 : ℝ) else 1) = ((S \ B).card : ℝ) := by
  rw [sum_ite]
  simp only [sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
  have he : S.filter (fun i => i ∉ B) = S \ B := by ext i; simp
  rw [he]

lemma sum_rank_indicators (m N : ℕ) :
    (∑ i ∈ range m, if N ≤ i then (1 : ℝ) else 0) = (m - N : ℕ) := by
  rw [sum_ite]
  simp only [sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have he : (range m).filter (fun i => N ≤ i) = Ico N m := by
    ext i
    simp [and_comm]
  rw [he, Nat.card_Ico]

lemma outside_card_bound {ι : Type*} [DecidableEq ι] (S B : Finset ι) :
    S.card - B.card ≤ (S \ B).card := by
  rw [card_sdiff]
  exact Nat.sub_le_sub_left (card_le_card inter_subset_left) _

/-- Pool rank probabilities, then sort them. Every prefix is bounded below
by the corresponding parent rank prefix. Dependence between ranks is arbitrary. -/
lemma rank_prefix {Ω : Type*} [Fintype Ω] {n : ℕ}
    (B : Ω → Finset (Fin n)) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (σ : Equiv.Perm (Fin n)) (m : ℕ) (hm : m ≤ n) :
    (∑ j ∈ range m, ∑ ω, w ω * (if (B ω).card ≤ j then (1 : ℝ) else 0)) ≤
      ∑ j ∈ range m, extend (fun i => ∑ ω, w ω * (if σ i ∈ B ω then (0 : ℝ) else 1)) j := by
  classical
  let e : Fin m → Fin n := fun i => σ ⟨i, lt_of_lt_of_le i.isLt hm⟩
  have heinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have ht := σ.injective h
    exact congrArg (fun i : Fin n => i.val) ht
  let S : Finset (Fin n) := univ.image e
  have hScard : S.card = m := by simp [S, card_image_of_injective _ heinj]
  have hright : (∑ j ∈ range m, extend (fun i => ∑ ω, w ω * (if σ i ∈ B ω then (0 : ℝ) else 1)) j) =
      ∑ i ∈ S, ∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    rw [show S = univ.image e from rfl, sum_image]
    · apply sum_congr rfl
      intro i _
      simp [extend, e, lt_of_lt_of_le i.isLt hm]
    · exact heinj.injOn
  rw [hright, sum_comm, sum_comm (s := S)]
  apply sum_le_sum
  intro ω _
  rw [← mul_sum, ← mul_sum, sum_rank_indicators, sum_outside]
  apply mul_le_mul_of_nonneg_left _ (hw ω)
  exact_mod_cast hScard ▸ outside_card_bound S (B ω)

lemma rank_total {Ω : Type*} [Fintype Ω] {n : ℕ}
    (B : Ω → Finset (Fin n)) (w : Ω → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ j ∈ range n, ∑ ω, w ω * (if (B ω).card ≤ j then (1 : ℝ) else 0)) =
      ∑ j ∈ range n, extend (fun i => ∑ ω, w ω * (if σ i ∈ B ω then (0 : ℝ) else 1)) j := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (extend _)]
  simp only [extend_fin]
  rw [Equiv.sum_comp σ (fun i => ∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1)), sum_comm, sum_comm (s := (univ : Finset (Fin n)))]
  apply sum_congr rfl
  intro ω _
  rw [← mul_sum, ← mul_sum, sum_rank_indicators, sum_outside]
  congr 2
  rw [card_sdiff]
  simp

/-- The convex superadditivity comparison for an arbitrary joint distribution
of integer rank indicators. Padding of parent ranks is automatic. -/
lemma convex_rank_sum {Ω : Type*} [Fintype Ω] {n : ℕ}
    (B : Ω → Finset (Fin n)) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hd : ∀ x, DifferentiableAt ℝ f x) :
    (∑ i : Fin n, f (∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1))) ≤
      ∑ j : Fin n, f (∑ ω, w ω * (if (B ω).card ≤ j.val then (1 : ℝ) else 0)) := by
  classical
  let p : Fin n → ℝ := fun i => ∑ ω, w ω * (if i ∈ B ω then 0 else 1)
  let σ := Tuple.sort p
  let x := extend (fun i => p (σ i))
  let y : ℕ → ℝ := fun j => ∑ ω, w ω * (if (B ω).card ≤ j then 1 else 0)
  have hmono : ∀ a b, a ≤ b → b < n → x a ≤ x b := by
    intro a b hab hbn
    have han : a < n := lt_of_le_of_lt hab hbn
    change extend _ a ≤ extend _ b
    simp only [extend, dite_eq_left han, dite_eq_left hbn]
    exact Tuple.monotone_sort p hab
  have hprefix : ∀ m ≤ n, ∑ i ∈ range m, y i ≤ ∑ i ∈ range m, x i :=
    fun m hm => rank_prefix B w hw σ m hm
  have htotal : ∑ i ∈ range n, y i = ∑ i ∈ range n, x i := rank_total B w σ
  have ht := convex_sum_of_prefix hf hd hmono hprefix htotal
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (x i)),
    ← Fin.sum_univ_eq_sum_range (fun i => f (y i))] at ht
  change (∑ i : Fin n, f (extend (fun j => p (σ j)) i.val)) ≤ _ at ht
  simp only [extend_fin] at ht
  rw [Equiv.sum_comp σ (fun i => f (p i))] at ht
  exact ht


lemma convex_rank_sum_type {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (B : Ω → Finset ι) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hd : ∀ x, DifferentiableAt ℝ f x) :
    (∑ i : ι, f (∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1))) ≤
      ∑ j : Fin (Fintype.card ι), f (∑ ω, w ω * (if (B ω).card ≤ j.val then (1 : ℝ) else 0)) := by
  classical
  let e := Fintype.equivFin ι
  let B' := fun ω => (B ω).image e
  have h := convex_rank_sum B' w hw hf hd
  have he : (∑ i : ι, f (∑ ω, w ω * (if i ∈ B ω then (0 : ℝ) else 1))) =
      ∑ i : Fin (Fintype.card ι), f (∑ ω, w ω * (if i ∈ B' ω then (0 : ℝ) else 1)) := by
    apply Fintype.sum_equiv e
    intro i
    simp [B', e.injective.mem_finset_image]
  rw [he]
  simpa only [B', card_image_of_injective _ e.injective] using h

lemma sum_below {k N : ℕ} (hN : N ≤ k) :
    (∑ a : Fin k, if a.val < N then (1 : ℕ) else 0) = N := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < N then (1 : ℕ) else 0), ← sum_filter]
  have h : (range k).filter (fun a => a < N) = range N := by
    ext a
    simp only [mem_filter, mem_range]
    omega
  rw [h]
  simp

/-- Source integer ranks: rank a (with zero-based index) is P(N ≤ a).
The probability law is joint, without independent-child assumptions. -/
def countRank {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (N : Ω → ℕ) (a : ℕ) : ℝ :=
  ∑ ω, w ω * (if N ω ≤ a then 1 else 0)

lemma countRank_range {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hws : ∑ ω, w ω = 1) (N : Ω → ℕ) (a : ℕ) : countRank w N a ∈ Set.Icc 0 1 := by
  constructor
  · exact sum_nonneg fun ω _ => mul_nonneg (hw ω) (by split_ifs <;> norm_num)
  · calc countRank w N a ≤ ∑ ω, w ω := by
           apply sum_le_sum
           intro ω _
           split_ifs <;> simp [hw ω]
         _ = 1 := hws

lemma countRank_expected {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hws : ∑ ω, w ω = 1)
    {k : ℕ} (N : Ω → ℕ) (hN : ∀ ω, N ω ≤ k) :
    (∑ a : Fin k, (1 - countRank w N a.val)) = ∑ ω, w ω * N ω := by
  classical
  have hcoord (a : Fin k) : 1 - countRank w N a.val =
      ∑ ω, w ω * (if a.val < N ω then (1 : ℝ) else 0) := by
    conv_lhs => lhs; rw [← hws]
    rw [countRank, ← sum_sub_distrib]
    apply sum_congr rfl
    intro ω _
    by_cases h : N ω ≤ a.val
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  simp_rw [hcoord]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  rw [← mul_sum]
  congr 1
  exact_mod_cast sum_below (hN ω)

lemma convex_count_superadditivity {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hws : ∑ ω, w ω = 1)
    {k : ℕ} (N : Ω → I → ℕ) (hN : ∀ ω, ∑ i, N ω i ≤ k)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hd : ∀ x, DifferentiableAt ℝ f x)
    (hf1 : f 1 = 0) :
    (∑ i : I, ∑ a : Fin k, f (countRank w (fun ω => N ω i) a.val)) ≤
      ∑ a : Fin k, f (countRank w (fun ω => ∑ i, N ω i) a.val) := by
  classical
  let B : Ω → Finset (I × Fin k) := fun ω => univ.filter (fun ia => ia.2.val < N ω ia.1)
  have hNi (ω : Ω) (i : I) : N ω i ≤ k :=
    (single_le_sum (fun j _ => Nat.zero_le (N ω j)) (mem_univ i)).trans (hN ω)
  have hB (ω : Ω) : (B ω).card = ∑ i, N ω i := by
    change (univ.filter (fun ia : I × Fin k => ia.2.val < N ω ia.1)).card = _
    rw [card_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    exact sum_below (hNi ω i)
  have ht := convex_rank_sum_type B w hw hf hd
  have hleft : (∑ ia : I × Fin k, f (∑ ω, w ω * (if ia ∈ B ω then (0 : ℝ) else 1))) =
      ∑ i : I, ∑ a : Fin k, f (countRank w (fun ω => N ω i) a.val) := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro a _
    congr 1
    apply sum_congr rfl
    intro ω _
    simp only [B, mem_filter, mem_univ, true_and]
    by_cases h : a.val < N ω i
    · simp [h, not_le.mpr h]
    · simp [h, le_of_not_gt h]
  rw [hleft] at ht
  have hright : (∑ a : Fin (Fintype.card (I × Fin k)), f (∑ ω, w ω *
      (if (B ω).card ≤ a.val then (1 : ℝ) else 0))) =
      ∑ a : Fin k, f (countRank w (fun ω => ∑ i, N ω i) a.val) := by
    simp_rw [hB]
    change (∑ a : Fin (Fintype.card (I × Fin k)), f (countRank w (fun ω => ∑ i, N ω i) a.val)) = _
    rw [Fin.sum_univ_eq_sum_range (fun a => f (countRank w (fun ω => ∑ i, N ω i) a)) (Fintype.card (I × Fin k)),
      Fin.sum_univ_eq_sum_range (fun a => f (countRank w (fun ω => ∑ i, N ω i) a)) k]
    by_cases hcard : k ≤ Fintype.card (I × Fin k)
    · symm
      apply sum_subset (range_mono hcard)
      intro a ha han
      have hak : k ≤ a := by simpa using han
      have hc : countRank w (fun ω => ∑ i, N ω i) a = 1 := by
        simp only [countRank, ite_eq_left ((hN _).trans hak), mul_one, hws]
      rw [hc, hf1]
    · have hempty : Fintype.card I = 0 := by
        simp only [Fintype.card_prod, Fintype.card_fin] at hcard
        nlinarith
      have : IsEmpty I := Fintype.card_eq_zero_iff.mp hempty
      simp [countRank, hws, hf1]
  rw [hright] at ht
  exact ht

end KServer.RankOrder

end
noncomputable section

namespace KServer.CompatibleBounds
open Finset
open KServer.RankFunctions KServer.RankOrder

/-- The two actual lower-bound sums on a conditional count distribution. -/
def L {Ω : Type*} [Fintype Ω] (k : ℕ) (w : Ω → ℝ) (N : Ω → ℕ) (z : ℝ) : ℝ :=
  ∑ a : Fin k, rank z (countRank w N a.val)
def M {Ω : Type*} [Fintype Ω] (k : ℕ) (w : Ω → ℝ) (N : Ω → ℕ) : ℝ :=
  ∑ a : Fin k, sizeRank (countRank w N a.val)

/-- Lemma superadditivity, with arbitrary dependence and empty child sets. -/
theorem compatible_bounds {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hws : ∑ ω, w ω = 1)
    {k : ℕ} (N : Ω → I → ℕ) (hN : ∀ ω, ∑ i, N ω i ≤ k)
    {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    (∑ i, L k w (fun ω => N ω i) z) ≤ L k w (fun ω => ∑ i, N ω i) z ∧
    (∑ i, M k w (fun ω => N ω i)) ≤ M k w (fun ω => ∑ i, N ω i) ∧
    M k w (fun ω => ∑ i, N ω i) ≤ ∑ ω, w ω * (∑ i, N ω i) := by
  refine ⟨convex_count_superadditivity w hw hws N hN (rank_convex hz)
    (fun p => (rank_derivative z p).differentiableAt) (rank_cutoff z (by norm_num [sstar])),
    convex_count_superadditivity w hw hws N hN sizeRank_convex
    (fun p => (sizeRank_derivative p).differentiableAt) sizeRank_one, ?_⟩
  calc M k w (fun ω => ∑ i, N ω i) ≤
      ∑ a : Fin k, (1 - countRank w (fun ω => ∑ i, N ω i) a.val) := by
        exact sum_le_sum fun a _ => sizeRank_le_complement (countRank_range w hw hws _ _)
    _ = _ := countRank_expected w hws _ hN

lemma sizeRank_antitone : Antitone sizeRank := by
  apply antitone_of_hasDerivAt_nonpos sizeRank_derivative
  intro p
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_max_right _ _)

lemma sizeRank_at_cutoff : sizeRank sstar = 1 / 36 := by norm_num [sizeRank, sstar]

lemma sizeRank_below_cutoff {p : ℝ} (hp : p ≤ sstar) : 1 / 36 ≤ sizeRank p := by
  rw [← sizeRank_at_cutoff]
  exact sizeRank_antitone hp

lemma rank_size_domination {z p : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (hp : 0 ≤ p) :
    rank z p ≤ 36 * sizeRank p := by
  by_cases hs : p ≤ sstar
  · have := sizeRank_below_cutoff hs
    have := (rank_range hz hp).2
    linarith
  · rw [rank_cutoff z (le_of_not_ge hs)]
    exact mul_nonneg (by norm_num) (sizeRank_nonneg p)

/-- Exact core/flex decomposition for one child's ranks; indexing zero-based
changes no values because countRank a is the source rank a+1. -/
lemma core_decomposition {k : ℕ} (p : Fin k → ℝ) (K : Finset (Fin k)) (z : ℝ)
    (hK : ∀ a ∈ K, p a ≤ pstar) :
    (∑ a, rank z (p a)) = K.card - (3 + z) * (∑ a ∈ K, p a) +
      ∑ a ∈ univ \ K, rank z (p a) := by
  classical
  have he : (∑ a ∈ K, rank z (p a)) = K.card - (3 + z) * (∑ a ∈ K, p a) := by
    calc (∑ a ∈ K, rank z (p a)) = ∑ a ∈ K, (1 - (3 + z) * p a) := by
           apply sum_congr rfl
           intro a ha
           rw [rank, ite_eq_left (hK a ha)]
      _ = _ := by rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, mul_sum]
  have hc : univ \ K = Kᶜ := by ext; simp
  rw [hc, ← he]
  exact (sum_add_sum_compl K (fun a => rank z (p a))).symm

lemma core_flex_domination {k : ℕ} (p : Fin k → ℝ) (K : Finset (Fin k))
    (hK : ∀ a ∈ K, p a ≤ pstar) (hp : ∀ a, 0 ≤ p a)
    {z : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) :
    (K.card : ℝ) + (∑ a ∈ univ \ K, rank z (p a)) ≤ 36 * ∑ a, sizeRank (p a) := by
  classical
  have hcore : (K.card : ℝ) ≤ ∑ a ∈ K, 36 * sizeRank (p a) := by
    calc (K.card : ℝ) = ∑ _a ∈ K, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun a ha => by
        have hps : pstar ≤ sstar := by norm_num [pstar, sstar]
        have := sizeRank_below_cutoff ((hK a ha).trans hps)
        linarith
  have hflex : (∑ a ∈ univ \ K, rank z (p a)) ≤ ∑ a ∈ univ \ K, 36 * sizeRank (p a) :=
    sum_le_sum fun a _ => rank_size_domination hz (hp a)
  calc _ ≤ (∑ a ∈ K, 36 * sizeRank (p a)) + ∑ a ∈ univ \ K, 36 * sizeRank (p a) := add_le_add hcore hflex
    _ = _ := by
      rw [show univ \ K = Kᶜ by ext; simp, sum_add_sum_compl, mul_sum]

lemma flex_parameter_slack {k : ℕ} (p : Fin k → ℝ) (F : Finset (Fin k))
    (hF : ∀ a ∈ F, pstar / 4 ≤ p a)
    {z z' : ℝ} (hz : z ∈ Set.Icc 0 (1 / 100 : ℝ)) (hzz : z ≤ z') :
    (z' - z) / 96 * (∑ a ∈ F, rank z (p a)) ≤
      (∑ a ∈ F, rank z (p a)) - (∑ a ∈ F, rank z' (p a)) := by
  rw [← sum_sub_distrib, mul_sum]
  apply sum_le_sum
  intro a ha
  have hc := mul_le_mul_of_nonneg_left (parameterSlope_compare hz (hF a ha)).1 (sub_nonneg.mpr hzz)
  rw [rank_parameter_affine z (p a), rank_parameter_affine z' (p a)]
  rw [rank_parameter_affine z (p a)] at hc
  nlinarith

end KServer.CompatibleBounds

end

end OAI
