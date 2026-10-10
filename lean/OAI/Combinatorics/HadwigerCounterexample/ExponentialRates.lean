import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

/-! # Exponential Rates -/

noncomputable section
namespace HadwigerCounterexample

open Filter Real
open scoped Topology

def bp (x : ℝ) := (2:ℝ)^x
@[simp] theorem bp_zero : bp 0 = 1 := by simp [bp]
@[simp] theorem bp_one : bp 1 = 2 := by simp [bp]
theorem bp_pos (x : ℝ) : 0 < bp x := by unfold bp; positivity
theorem bp_nat (x : ℕ) : bp x = (2:ℝ)^x := by simp [bp]
theorem bp_add (x y : ℝ) : bp (x+y) = bp x * bp y :=
  Real.rpow_add (by norm_num) _ _
theorem bp_sub (x y : ℝ) : bp (x-y) = bp x / bp y :=
  Real.rpow_sub (by norm_num) _ _
theorem bp_neg (x : ℝ) : bp (-x) = (bp x)⁻¹ := by simpa using bp_sub 0 x
theorem bp_mul_nat (x : ℝ) (n : ℕ) : bp (x*n) = bp x ^ n := by
  unfold bp; rw [Real.rpow_mul (by norm_num)]; simp
@[gcongr] theorem bp_le {x y : ℝ} (h : x ≤ y) : bp x ≤ bp y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h
@[gcongr] theorem bp_lt {x y : ℝ} (h : x < y) : bp x < bp y :=
  Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
theorem log_bp (x : ℝ) : log (bp x) = x * log 2 := Real.log_rpow (by norm_num) _

theorem bp_poly_dom {a : ℝ} (ha : 0 < a) (c d : ℝ) :
    ∀ᶠ x : ℝ in atTop, c*x^d < bp (a*x) := by
  have hla : 0 < Real.log 2 * a := mul_pos (Real.log_pos (by norm_num)) ha
  have h := tendsto_exp_mul_div_rpow_atTop d _ hla
  filter_upwards [h.eventually (eventually_gt_atTop c), eventually_gt_atTop (0:ℝ)] with x hx hx'
  change c < Real.exp ((Real.log 2*a)*x)/x^d at hx
  rw [lt_div_iff₀ (by positivity)] at hx
  rwa [bp, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← mul_assoc]

theorem bp_poly_dom_nat {a : ℝ} (ha : 0 < a) (c : ℝ) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, c*(n:ℝ)^d < bp (a*n) := by
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (bp_poly_dom ha c d)
  simpa using h

theorem bp_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (a*x)) atTop atTop :=
  (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
    ((tendsto_const_mul_atTop_of_pos ha).mpr tendsto_id)

theorem bp_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => bp (-a*x)) atTop (𝓝 0) := by
  simp_rw [neg_mul,bp_neg]
  exact (bp_tendsto ha).inv_tendsto_atTop

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}

/-- Exponentially small at scale n. -/
def ExpSmall (l : Filter ι) (n f : ι → ℝ) :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, |f i| ≤ bp (-c * n i)

/-- Subexponential upper bound at scale n. -/
def ExpO (l : Filter ι) (n f : ι → ℝ) :=
  ∀ c : ℝ, 0 < c → ∀ᶠ i in l, |f i| ≤ bp (c * n i)

namespace ExpSmall
theorem mono (hf : ExpSmall l n f) (h : ∀ᶠ i in l, |g i| ≤ |f i|) : ExpSmall l n g := by
  rcases hf with ⟨c,hc,hf⟩
  exact ⟨c,hc, h.and hf |>.mono fun _ ⟨h,g⟩ => h.trans g⟩

theorem zero (l : Filter ι) (n : ι → ℝ) : ExpSmall l n (fun _ => 0) := by
  refine ⟨1, by norm_num, .of_forall fun _ => ?_⟩
  rw [abs_zero]; exact (bp_pos _).le

theorem mul (hf : ExpSmall l n f) (hg : ExpO l n g) :
    ExpSmall l n (fun i => f i*g i) := by
  obtain ⟨c,hc,h⟩ := hf
  refine ⟨c/2,by linarith,?_⟩
  filter_upwards [h,hg (c/2) (by linarith)] with i hi hj
  rw [abs_mul, show -(c/2)*n i = -c*n i + c/2*n i by ring, bp_add]
  exact mul_le_mul hi hj (abs_nonneg _) (bp_pos _).le

theorem add (hn : Tendsto n l atTop) (hf : ExpSmall l n f) (hg : ExpSmall l n g) :
    ExpSmall l n (fun i => f i+g i) := by
  obtain ⟨c,hc,h⟩ := hf; obtain ⟨d,hd,h'⟩ := hg
  let a := min c d
  have ha : 0 < a := lt_min hc hd
  refine ⟨a/2,by linarith, ?_⟩
  filter_upwards [h,h',hn.eventually (eventually_ge_atTop 0),
    ((bp_tendsto (show 0 < a/2 by linarith)).comp hn).eventually
      (eventually_ge_atTop 2)] with i hi hj hx hb
  change 2 ≤ bp (a/2*n i) at hb
  have h₁ : -c*n i ≤ -a*n i := by gcongr; exact min_le_left _ _
  have h₂ : -d*n i ≤ -a*n i := by gcongr; exact min_le_right _ _
  refine le_trans (abs_add_le _ _) ?_
  rw [show -(a/2)*n i = a/2*n i + -a*n i by ring,bp_add]
  calc |f i| + |g i| ≤ bp (-a*n i)+bp (-a*n i) :=
         add_le_add (hi.trans (bp_le h₁)) (hj.trans (bp_le h₂))
       _ = 2*bp (-a*n i) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hb (bp_pos _).le

theorem lim (hn : Tendsto n l atTop) (hf : ExpSmall l n f) :
    Tendsto f l (𝓝 0) := by
  obtain ⟨c,hc,h⟩ := hf
  have hl := (bp_tendsto_zero hc).comp hn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ hl
    (h.mono fun i hi => (abs_le.mp hi).1)
    (h.mono fun i hi => (abs_le.mp hi).2)
  simpa using hl.neg
end ExpSmall

theorem expO_const (hn : Tendsto n l atTop) (b : ℝ) :
    ExpO l n (fun _ => b) := fun _ hc =>
  ((bp_tendsto hc).comp hn).eventually (eventually_ge_atTop _)

end HadwigerCounterexample

end

end OAI
