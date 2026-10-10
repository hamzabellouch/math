import OAI.Analysis.FourierLLogL.Snapshot.Display
/-! # An unnormalized divergence paying for changes of portrait -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture
variable {M : ℕ} {α β : Type} [Fintype α] [Fintype β]
open scoped Classical

def grain (a b : ℝ) := (a-b)^2/(a+b)
def cloud (a b : α → ℝ) := ∑ i, grain (a i) (b i)

lemma grain_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ grain a b :=
    div_nonneg (sq_nonneg _) (by linarith)

lemma cloud_nonneg (a b : α → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ cloud a b := Finset.sum_nonneg fun _ _ => grain_nonneg (ha _) (hb _)

lemma cloud_same (a : α → ℝ) : cloud a a=0 := by simp [cloud,grain]

lemma distance_cloud (a b : α → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (distance a b)^2 ≤ ((∑ i,a i)+ ∑ i,b i)*cloud a b := by
  unfold distance cloud; rw [← Finset.sum_add_distrib]
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
    (fun i _ => add_nonneg (ha _) (hb _)) (fun i _ => grain_nonneg (ha i) (hb i)) ?_
  intro i _
  rw [sq_abs,grain]
  rcases lt_or_eq_of_le (add_nonneg (ha i) (hb i)) with hi|hi
  · exact le_of_eq (by field_simp)
  · have hx := ha i; have hy := hb i
    rw [show a i = 0 by linarith,show b i = 0 by linarith]; simp

private lemma shift_formula (a b : ℝ) (h : a+b ≠ 0) :
    grain a b=a-3*b+4*b^2/(a+b) := by unfold grain; field_simp; ring

lemma grain_shrinks (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : b ≤ a) (ht : 0 ≤ t) :
    grain b t ≤ grain a t + 4*(a-b) := by
  rcases eq_or_lt_of_le ht with H|H
  · have HH (a : ℝ) : grain a 0=a := by
      unfold grain; by_cases h : a=0 <;> simp [h, pow_two]
    rw [← H,HH,HH]; linarith
  · rw [shift_formula _ _ (by linarith),shift_formula _ _ (by linarith)]
    apply le_of_sub_nonneg
    have hx : 0 < (a+t)*(b+t) := by positivity
    apply le_of_mul_le_mul_left ?_ hx
    rw [mul_zero]
    have HE : t^2 ≤ (a+t)*(b+t) := by nlinarith
    have HT := mul_le_mul_of_nonneg_right HE (show 0 ≤ a-b by linarith)
    have HZ :
        (a+t)*(b+t)*((a-3*t+4*t^2/(a+t)+4*(a-b)) - (b-3*t+4*t^2/(b+t))) =
          (a-b)*(5*((a+t)*(b+t))-4*t^2) := by field_simp; ring
    rw [HZ]; nlinarith

/-- comparison curvature cost at a spatial step is controlled by the Fisher charge -/
lemma grain_average (a b m t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (h : a+b=2*m) :
    (grain a t+grain b t)/2 ≤ grain m t +4*((a-b)/2)^2/m := by
  rcases eq_or_lt_of_le ht with H|H
  · have he (a : ℝ) : grain a 0=a := by
      unfold grain; by_cases h : a=0 <;> simp [h,pow_two]
    rw [← H,he,he,he]
    have HH : 0 ≤ 4*((a-b)/2)^2/m := div_nonneg (by positivity) (by linarith)
    linarith
  have hm : 0 ≤ m := by linarith
  rcases eq_or_lt_of_le hm with Hm|Hm
  · have he : a=m := by linarith
    have hh : b=m := by linarith
    rw [he,hh]; ring_nf; exact le_rfl
  rw [shift_formula _ _ (by linarith),shift_formula _ _ (by linarith),shift_formula _ _ (by linarith)]
  let d := (a-b)/2
  have he : t^2*m ≤ (a+t)*(b+t)*(m+t) := by
    have hH : t^2 ≤ (a+t)*(b+t) := by nlinarith
    exact mul_le_mul hH (by linarith) hm (by positivity)
  have hi :
      ((a-3*t+4*t^2/(a+t))+(b-3*t+4*t^2/(b+t)))/2 - (m-3*t+4*t^2/(m+t))
        = 4*t^2*d^2/((a+t)*(b+t)*(m+t)) := by
    unfold d
    field_simp
    rw [show m=(a+b)/2 by linarith]
    ring
  rw [add_comm (m-3*t+4*t^2/(m+t))]; apply sub_le_iff_le_add.mp

  rw [hi]
  change 4*t^2*d^2/((a+t)*(b+t)*(m+t)) ≤ 4*d^2/m
  apply (div_le_div_iff₀ (by positivity) Hm).mpr
  nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg d)]

lemma cloud_kill {s q : Scene M} (h : Less s q) (hh : ReadyAt s) (hv : ReadyAt q)
    (hp : 0 ≤ s.norm) (k : Grid M → Law α) (a : α → ℝ) (ha : ∀ i, 0 ≤ a i) :
    cloud (hist q k) a ≤ cloud (hist s k) a+4*(share s-share q) := by
  have H : 0 ≤ q.norm := by rw [h.flat]; exact hp
  rw [← total_hist _ hh.1 k, ← total_hist _ hv.1 k]
  unfold cloud; rw [← Finset.sum_sub_distrib,Finset.mul_sum,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => grain_shrinks _ _ _
    (nonnegative_hist s hh.2 hp k i) (nonnegative_hist q hv.2 H k i) (hist_le h hh hp k i) (ha _)

lemma cloud_drift (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (hs : 0 ≤ s.wage) (he : 0 ≤ s.norm) (k : Grid M → Law α)
    (t : α → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (uniform Bool).Ex (fun b => cloud (hist (s.smaller b) k) t) ≤
      cloud (hist s k) t+4*fisher s k := by
  let p (i) := hist (s.smaller false) k i; let q (i) := hist (s.smaller true) k i
  let m (i) := hist s k i
  have hi i : (grain (p i) (t i)+grain (q i) (t i))/2 ≤
      grain (m i) (t i) +4*(Procedure.diff s k i)^2/m i := by
    apply grain_average
    · exact nonnegative_hist (s.smaller false) hs he k _
    · exact nonnegative_hist (s.smaller true) hs he k _
    · exact ht _
    · exact hist_split _ hp hh k _
  calc
    _ = ∑ i,(grain (p i) (t i)+grain (q i) (t i))/2 := by
      unfold cloud; rw [← Finset.sum_div,Finset.sum_add_distrib,Ex,Fintype.sum_bool]
      simp only [uniform_apply,Fintype.card_bool,Nat.cast_ofNat]
      unfold p q; ring
    _ ≤ _ := Finset.sum_le_sum (s:=Finset.univ) fun i _ => hi i
    _ = _ := by simp_rw [fisher,cloud,mul_div_assoc,Finset.mul_sum,Finset.sum_add_distrib]; rfl

end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI
