import OAI.Analysis.FourierLLogL.Paths.Trip
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


variable {E : Type*}

/-- A predictable linear wager driven by the revealed output bit, with quadratic cost. -/
structure Desk (M : ℕ) (E : Type*) where
  stake : E → Scene M → Scene M → ℝ
  stepAt : E → Beat M → E

namespace Desk

def single (x : ℝ) (i : Bool) := curl i*x-x^2/2
def pay (A : Desk M E) (e : E) (b : Beat M) :=
    single (A.stake e b.pre b.post) b.bit
def tally (A : Desk M E) (e : E) : Path M → ℝ
  | [] => 0
  | b::l => pay A e b + tally A (stepAt A e b) l

def peak (A : Desk M E) (e : E) (a r : ℝ) : Path M → ℝ
  | [] => r
  | b::l => let x := a+ A.pay e b; peak A (stepAt A e b) x (max r x) l

lemma peak_base (A : Desk M E) (e : E) (a r : ℝ) (l : Path M) :
    r ≤ peak A e a r l := by
  induction l generalizing e a r with
  | nil => exact le_rfl
  | cons b l ih =>
    apply le_trans (le_max_left r (a+A.pay e b))
    apply ih

lemma peak_on (A : Desk M E) (e : E) (a r : ℝ) (h : a ≤ r) (l m : Path M) :
    a+tally A e l ≤ peak A e a r (l++m) := by
  induction l generalizing e a r with
  | nil => simpa only [List.nil_append,tally,add_zero] using h.trans (peak_base A e a r m)
  | cons b l ih =>
    rw [tally,← add_assoc]; exact ih _ _ _ (le_max_right r _)

def heatW (A : Desk M E) (e : E) (l : Path M) :=
    exp (peak A e 0 0 l/2)

lemma heatW_one (A : Desk M E) (e : E) (l : Path M) : 1 ≤ heatW A e l :=
    one_le_exp (by linarith [peak_base A e 0 0 l])
lemma edge_score (A : Desk M E) (e : E) (l m : Path M) :
    A.tally e l ≤ 2*log (heatW A e (l++m)) := by
  rw [heatW,log_exp]; linarith [peak_on A e 0 0 (le_refl _) l m]

private def purses (a r : ℝ) := exp (r/2)+exp (a-r/2)
private lemma purses_high (a r : ℝ) : purses a (max r a) ≤ purses a r := by
  cases le_total a r with
  | inl h => rw [max_eq_left h]
  | inr h =>
    rw [max_eq_right h]; unfold purses
    let x := exp (r/4); let y := exp (a/2-r/4)
    have h1 : exp (r/2)=x^2 := by unfold x; rw [pow_two,← exp_add]; ring_nf
    have h2 : exp (a-r/2)=y^2 := by unfold y; rw [pow_two,← exp_add]; ring_nf
    have h3 : exp (a/2)=x*y := by unfold x y; rw [← exp_add]; ring_nf
    rw [show a-a/2=a/2 by ring,h1,h2,h3]; nlinarith [sq_nonneg (x-y)]

private lemma single_mean (x : ℝ) :
    (uniform Bool).Ex (fun i => exp (single x i)) ≤ 1 := by
  rw [fair_av]; unfold single
  change (exp (1*x-x^2/2)+exp (-1*x-x^2/2))/2 ≤ _
  rw [one_mul,neg_one_mul,exp_sub,exp_sub,← add_div,
    div_right_comm (_+_) (exp _),← cosh_eq]
  exact (div_le_one (exp_pos _)).mpr (cosh_le_exp_half_sq _)

lemma peak_mean (A : Desk M E) (t : Thread M s) (h : t.Following j J f) (e : E) (a r : ℝ) :
    (s.here.dice M).Ex (fun x => exp (peak A e a r (t.stream x)/2)) ≤
      exp (r/2)+exp (a-r/2) := by
  induction t generalizing e a r with
  | blank s =>
    change (s.here.dice M).Ex (fun _ => exp (r/2)) ≤ _
    rw [Ex_const]; exact le_add_of_nonneg_right (exp_pos _).le
  | ran s q k ih =>
    rw [stream_branch _ h (fun l _ => exp (peak A e a r l/2))]
    let p := A.stake e s q
    let w (b : Bool) := a+single p b
    let P := uniform Bool
    apply le_trans (b:=P.Ex fun i => purses (w i) r)
    · apply Ex_mono; intro b
      exact le_trans (ih b (h.2.2.2.2.2 b) _ _ _) (purses_high (w b) r)
    simp only [purses,w]
    have H (i : Bool) : exp (a+single p i-r/2)=exp (a-r/2)*exp (single p i) := by
      rw [← exp_add]; congr 1; ring
    simp_rw [H,Ex_add _ (f:=fun _ => _),Ex_const,Ex_lmul]
    apply add_le_add_right
    exact mul_le_of_le_one_right (exp_pos _).le (single_mean _)

lemma heat_bound (A : Desk M E) (t : Thread M s) (h : t.Following j J f) (e : E) :
    (s.here.dice M).Ex (fun x => A.heatW e (t.stream x)) ≤ 2 := by
  have H := A.peak_mean t h e 0 0
  change (s.here.dice M).Ex (fun x => A.heatW e (t.stream x)) ≤ _ at H
  norm_num at H; exact H

end Desk


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
