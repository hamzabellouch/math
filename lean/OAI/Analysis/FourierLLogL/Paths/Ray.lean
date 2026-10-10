import OAI.Analysis.FourierLLogL.Paths.Gust
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Beam
def content (v w : ℂ) (x : ℝ) := ‖v‖^2+‖w‖^2+x^2
def ray (v w : ℂ) (x : ℝ) := √(content v w x)

lemma content_pos (v w : ℂ) (x : ℝ) : 0 ≤ content v w x := by unfold content; positivity
lemma ray_pos (v w : ℂ) (x : ℝ) : 0 ≤ ray v w x := sqrt_nonneg _
lemma ray_sq (v w : ℂ) (x : ℝ) : ray v w x^2=content v w x :=
    Real.sq_sqrt (content_pos _ _ _)
lemma ray_bounds (v w : ℂ) (x : ℝ) : let r := ray v w x
    ‖v‖ ≤ r ∧ ‖w‖ ≤ r ∧ |x| ≤ r ∧ r ≤ ‖v‖+‖w‖+|x| := by
  intro r
  have hr : 0 ≤ r := ray_pos _ _ _
  have HH : r^2=‖v‖^2+‖w‖^2+x^2 := ray_sq _ _ _
  have hv := norm_nonneg v; have hw := norm_nonneg w; have hx := abs_nonneg x
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [sq_abs x]

/-- Unit linearization of an output triple -/
def glow (v w : ℂ) (x : ℝ) (a b : ℂ) (t : ℝ) :=
    (duet v a+duet w b+x*t) / ray v w x

lemma glow_add (v w : ℂ) (x : ℝ) (a b c d : ℂ) (h k : ℝ) :
    glow v w x (a+c) (b+d) (h+k)=glow v w x a b h+glow v w x c d k := by
  rw [glow,glow,glow,duet_add,duet_add]; ring
lemma glow_scale (v w : ℂ) (x y h : ℝ) (a b : ℂ) :
    glow v w x ((y:ℂ)*a) ((y:ℂ)*b) (y*h)=y*glow v w x a b h := by
  rw [glow,glow,duet_scale,duet_scale]; ring

lemma glow_limit (v w : ℂ) (x : ℝ) (a b : ℂ) (t : ℝ) :
    |glow v w x a b t| ≤ ‖a‖+‖b‖+|t| := by
  let r := ray v w x
  have H := ray_bounds v w x
  have hr : 0 ≤ r := ray_pos v w x
  unfold glow
  rcases eq_or_lt_of_le hr with h|h
  · change |_/r| ≤ _
    rw [←h,div_zero,abs_zero]; positivity
  change |_/r| ≤ _
  rw [abs_div,abs_of_nonneg hr]
  apply (div_le_iff₀ h).mpr
  have he := abs_add_le (duet v a+duet w b) (x*t)
  have hi := abs_add_le (duet v a) (duet w b)
  rw [abs_mul] at he
  change ‖v‖ ≤ r ∧ _ at H
  have h1 : ‖v‖ ≤ r := H.1
  have h2 : ‖w‖ ≤ r := H.2.1
  have h3 : |x| ≤ r := H.2.2.1
  nlinarith [norm_nonneg a,norm_nonneg b,abs_nonneg t,duet_limit v a,duet_limit w b]

lemma ray_shift (v w a b : ℂ) (x t : ℝ) (C : ℝ) (hc : 0 ≤ C)
    (h : content a b t ≤ ray v w x*C) :
    ray (v+a) (w+b) (x+t) ≤ ray v w x+glow v w x a b t+C := by
  let r := ray v w x; let d := glow v w x a b t
  rcases eq_or_lt_of_le (show 0 ≤ r from ray_pos _ _ _) with he|he
  · have hh : content a b t ≤ 0 := by change _ ≤ r*C at h; rwa [←he,zero_mul] at h
    unfold content at hh
    have hA : a=0 := norm_le_zero_iff.mp (by nlinarith)
    have hB : b=0 := norm_le_zero_iff.mp (by nlinarith)
    have hT : t=0 := by nlinarith
    simp [hA,hB,hT,glow,duet_zero,hc]
  · let R := ray (v+a) (w+b) (x+t)
    have hH : R^2=r^2+2*r*d+content a b t := by
      have H : r*d=duet v a+duet w b+x*t := by
        unfold d glow; change r*(_/r)=_
        field_simp
      rw [show 2*r*d=2*(r*d) by ring,H]
      unfold R r
      rw [ray_sq,ray_sq,content,content,content,duet_inc,duet_inc]
      ring
    change R ≤ r+d+C
    change _ ≤ r*C at h
    nlinarith [sq_nonneg (R-r)]

lemma ray_slide (v w : ℂ) (x : ℝ) (a : ℂ) (t : ℝ) :
    ray v (w+a) (x+t) ≤ ray v w x + ‖a‖ + |t| := by
  let r := ray v w x; let d := ray v (w+a) (x+t)
  have H := ray_bounds v w x
  have hR : r^2 = ‖v‖^2+‖w‖^2+x^2 := ray_sq _ _ _
  have hr : 0 ≤ r := ray_pos _ _ _
  have hd : d^2=‖v‖^2+‖w+a‖^2+(x+t)^2 := ray_sq _ _ _
  have hi : ‖w‖ ≤ r := H.2.1
  have Hq : |x| ≤ r := H.2.2.1
  change d ≤ _
  have HH : ‖w+a‖^2 ≤ (‖w‖+‖a‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le w a) _
  have Ht : x*t ≤ r*|t| := (le_abs_self _).trans
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right Hq (abs_nonneg t))
  change d ≤ r+_
    + |t|
  nlinarith [sq_abs t,norm_nonneg a,abs_nonneg t]


def prism (s : Scene M) (u : Grid M) (W : Paths.Vector M) (a : ℝ) (z : Grid M) :=
    ray (W z) (letter s u z) (a*matter s z)
def watt (s : Scene M) (u : Grid M) (W : Paths.Vector M) (a : ℝ) := ∑ z, prism s u W a z
def yieldW (W : Paths.Vector M) := ∑ i : Grid M, ‖W i‖
lemma yield_step (s : Scene M) (u : Grid M) (W : Paths.Vector M) (a : ℝ) :
    yieldW W ≤ watt s u W a := Finset.sum_le_sum fun i _ => (ray_bounds (W i) _ _).1

lemma watt_idle {s : Scene M} (h : Fit s) (u : Grid M) (a : ℝ) (ha : 0 ≤ a) (hx : a ≤ 1) :
    watt s u 0 a ≤ 8 := by
  apply le_trans (b:=∑ i,2*matter s i)
  · apply Finset.sum_le_sum; intro i _
    change ray 0 _ _ ≤ _
    apply le_trans (ray_bounds _ _ _).2.2.2
    have HM := matter_norm h u i; have hM := matter_nonneg h i
    rw [abs_of_nonneg (mul_nonneg ha hM),norm_zero]
    nlinarith
  rw [←Finset.mul_sum,matter_sum h]
  linarith [h.lift]

lemma watt_slide {b : Beat M} (h : Ideal b.pre b.post) (u : Grid M) (W : Paths.Vector M) (a : ℝ)
    (ha : 0 ≤ a) (he : a ≤ 1) :
    watt b.post u W a ≤ watt b.pre u W a + 2*killed b := by
  let f := letter b.pre u; let g := letter b.post u
  let p := matter b.pre; let q := matter b.post
  rw [h.kill_eq,←matter_sum h.fit,←matter_sum h.climb.fit,← Finset.sum_sub_distrib,
    Finset.mul_sum,watt,watt,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  change ray (W i) (g i) (a*q i) ≤ ray (W i) (f i) (a*p i)+_
  conv_lhs =>
    rw [show g i=f i+(g i-f i) by ring,show a*q i=a*p i+a*(q i-p i) by ring]
  apply le_trans (ray_slide (W i) _ _ _ _)
  have H : ‖f i-g i‖ ≤ p i-q i := matter_drain h u i
  have HH := (norm_nonneg _).trans H
  rw [abs_mul,abs_of_nonneg ha,abs_sub_comm,abs_of_nonneg HH,norm_sub_rev]
  change _ ≤ _+2*(p i-q i)
  nlinarith

end Beam


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
