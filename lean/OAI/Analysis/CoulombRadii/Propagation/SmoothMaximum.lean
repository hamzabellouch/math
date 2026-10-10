import Mathlib
import OAI.Analysis.CoulombRadii.Variational.WeakLaplacian

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

def softAbs (e x : ℝ) := Real.sqrt (x^2+e^2)
def softSlope (e x : ℝ) := x/softAbs e x
def softWeight (e x : ℝ) := (1+softSlope e x)/2
def softPlus (e x : ℝ) := (x+softAbs e x)/2
def softMax (e a b : ℝ) := b+softPlus e (a-b)

lemma softAbs_pos {e : ℝ} (he : 0<e) (x : ℝ) : 0<softAbs e x := by
  unfold softAbs
  exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])

lemma softAbs_sq (e x : ℝ) : (softAbs e x)^2=x^2+e^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma abs_le_softAbs (e x : ℝ) : |x|≤ softAbs e x := by
  have hp : 0≤ softAbs e x := Real.sqrt_nonneg _
  nlinarith [softAbs_sq e x,sq_abs x,sq_nonneg e,abs_nonneg x]

lemma softWeight_bounds {e : ℝ} (he : 0<e) (x : ℝ) : 0≤ softWeight e x ∧ softWeight e x≤1 := by
  have ha := abs_le_softAbs e x
  have hl : -1≤ softSlope e x := (le_div_iff₀ (softAbs_pos he x)).mpr (by linarith [neg_abs_le x])
  have hu : softSlope e x≤1 := (div_le_iff₀ (softAbs_pos he x)).mpr (by linarith [le_abs_self x])
  unfold softWeight
  constructor <;> linarith

lemma softAbs_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softAbs e) (softSlope e x) x := by
  have h := (((hasDerivAt_id x).pow 2).add_const (e^2)).sqrt
    (show x^2+e^2≠0 by nlinarith [sq_nonneg x])
  convert h using 1
  · rfl
  · dsimp [softSlope,softAbs]
    field_simp

lemma softSlope_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softSlope e) (e^2/(softAbs e x)^3) x := by
  have hp := ne_of_gt (softAbs_pos he x)
  have H := (hasDerivAt_id x).div (softAbs_hasDerivAt he x) hp
  have heq : (1*softAbs e x-x*softSlope e x)/(softAbs e x)^2=e^2/(softAbs e x)^3 := by
    dsimp only [softSlope]
    field_simp [hp]
    nlinarith [softAbs_sq e x]
  change HasDerivAt (softSlope e) ((1*softAbs e x-x*softSlope e x)/(softAbs e x)^2) x at H
  rw [heq] at H
  exact H

lemma softPlus_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softPlus e) (softWeight e x) x := by
  exact ((hasDerivAt_id x).add (softAbs_hasDerivAt he x)).div_const 2

lemma softWeight_hasDerivAt {e : ℝ} (he : 0<e) (x : ℝ) :
    HasDerivAt (softWeight e) (e^2/(2*(softAbs e x)^3)) x := by
  have H := ((softSlope_hasDerivAt he x).const_add 1).div_const 2
  have heq : (e^2/(softAbs e x)^3)/2=e^2/(2*(softAbs e x)^3) := by ring
  rw [heq] at H
  exact H

lemma contDiff_softAbs {e : ℝ} (he : 0<e) : ContDiff ℝ ∞ (softAbs e) := by
  apply (contDiff_id.pow 2 |>.add contDiff_const).sqrt
  intro x
  nlinarith [sq_nonneg x]

lemma contDiff_softPlus {e : ℝ} (he : 0<e) : ContDiff ℝ ∞ (softPlus e) :=
  (contDiff_id.add (contDiff_softAbs he)).div_const 2

lemma contDiff_softMax {e : ℝ} (he : 0<e) {f g : Position → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => softMax e (f x) (g x)) :=
  hg.add ((contDiff_softPlus he).comp (hf.sub hg))

lemma second_deriv_comp_scalar {f h : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hh : ContDiff ℝ 2 h) (x : ℝ) :
    deriv (deriv (fun t => h (f t))) x=
      deriv (deriv h) (f x)*(deriv f x)^2+deriv h (f x)*deriv (deriv f) x := by
  have hd : deriv (fun t => h (f t))=fun t => deriv h (f t)*deriv f t := by
    funext t
    exact ((hh.differentiable (by norm_num) (f t)).hasDerivAt.comp t
      (hf.differentiable (by norm_num) t).hasDerivAt).deriv
  rw [hd]
  have hh' : Differentiable ℝ (deriv h) := hh.differentiable_deriv_two
  have hf' : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have H := ((hh' (f x)).hasDerivAt.comp x (hf.differentiable (by norm_num) x).hasDerivAt).mul
    (hf' x).hasDerivAt
  change deriv ((deriv h ∘ f)*deriv f) x=_
  rw [H.deriv]
  simp only [Function.comp_def]
  ring

lemma second_deriv_softPlus {e : ℝ} (he : 0<e) (x : ℝ) :
    deriv (deriv (softPlus e)) x=e^2/(2*(softAbs e x)^3) := by
  have h : deriv (softPlus e)=softWeight e := funext (fun x => (softPlus_hasDerivAt he x).deriv)
  rw [h]
  exact (softWeight_hasDerivAt he x).deriv

lemma coordinateLaplacian_comp_scalar {f : Position → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ 2 h) (x : Position) :
    coordinateLaplacian (fun y => h (f y)) x=
      deriv (deriv h) (f x)*(∑ a : Fin 3, (deriv (fun t : ℝ => f (x+t • axis a)) 0)^2)+
      deriv h (f x)*coordinateLaplacian f x := by
  unfold coordinateLaplacian
  have H (a : Fin 3) : ContDiff ℝ 2 (fun t : ℝ => f (x+t • axis a)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  simp_rw [second_deriv_comp_scalar (H _) hh,zero_smul,add_zero]
  rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]

lemma coordinateLaplacian_softMax_lower {e : ℝ} (he : 0<e) {f g : Position → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Position) :
    softWeight e (f x-g x)*coordinateLaplacian f x+
      (1-softWeight e (f x-g x))*coordinateLaplacian g x≤
      coordinateLaplacian (fun y => softMax e (f y) (g y)) x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by exact WithTop.coe_le_coe.mpr le_top)
  have hs2 : ContDiff ℝ 2 (softPlus e) := (contDiff_softPlus he).of_le (by exact WithTop.coe_le_coe.mpr le_top)
  unfold softMax
  have hcomp : ContDiff ℝ 2 (fun y => softPlus e (f y-g y)) := hs2.comp (hf2.sub hg2)
  rw [coordinateLaplacian_add_at hg2.contDiffAt hcomp.contDiffAt,
    coordinateLaplacian_comp_scalar (hf2.sub hg2) hs2,second_deriv_softPlus he,
    (softPlus_hasDerivAt he _).deriv,coordinateLaplacian_sub hf2 hg2]
  have H : 0≤e^2/(2*(softAbs e (f x-g x))^3)*
      (∑ a : Fin 3, (deriv (fun t : ℝ => f (x+t • axis a)-g (x+t • axis a)) 0)^2) := by
    apply mul_nonneg
    · have hp := softAbs_pos he (f x-g x)
      positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

lemma softAbs_le {e : ℝ} (he : 0≤ e) (x : ℝ) : softAbs e x≤ |x|+e := by
  have h := softAbs_sq e x
  have h0 : 0≤ softAbs e x := Real.sqrt_nonneg _
  nlinarith [abs_nonneg x,sq_abs x,mul_nonneg (abs_nonneg x) he]

lemma softMax_zero (a b : ℝ) : softMax 0 a b=max a b := by
  unfold softMax softPlus softAbs
  simp only [zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs]
  by_cases h : b≤ a
  · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_left h]
    ring
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)),max_eq_right (le_of_not_ge h)]
    ring

lemma softMax_bounds {e : ℝ} (he : 0≤ e) (a b : ℝ) :
    max a b≤ softMax e a b ∧ softMax e a b≤ max a b+e/2 := by
  have h1 := abs_le_softAbs e (a-b)
  have h2 := softAbs_le he (a-b)
  have hz := softMax_zero a b
  unfold softMax softPlus softAbs at hz
  simp only [zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs] at hz
  unfold softMax softPlus
  constructor <;> linarith

lemma softMax_abs_le {e a b A B : ℝ} (he : 0≤ e) (ha : |a|≤ A) (hb : |b|≤ B) :
    |softMax e a b|≤ A+B+e := by
  have h := softMax_bounds he a b
  have hA := (abs_nonneg a).trans ha
  have hB := (abs_nonneg b).trans hb
  have hu : max a b≤ A+B := max_le (by linarith [(le_abs_self a).trans ha]) (by linarith [(le_abs_self b).trans hb])
  have hl : -(A+B)≤ max a b := by linarith [(abs_le.mp ha).1,le_max_left a b]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma softMax_tendsto {e a b : ℕ → ℝ} {A B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    Tendsto (fun n => softMax (e n) (a n) (b n)) atTop (𝓝 (max A B)) := by
  have h := hb.add (((ha.sub hb).add (((ha.sub hb).pow 2).add (he.pow 2)).sqrt).div_const 2)
  simpa only [softMax,softPlus,softAbs,←softMax_zero] using h

lemma softWeight_tendsto_of_lt {e a b : ℕ → ℝ} {A B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hAB : B<A) : Tendsto (fun n => softWeight (e n) (a n-b n)) atTop (𝓝 1) := by
  have hs : Tendsto (fun n => softAbs (e n) (a n-b n)) atTop (𝓝 (A-B)) := by
    have H := (((ha.sub hb).pow 2).add (he.pow 2)).sqrt
    simpa only [softAbs,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs,
      abs_of_pos (sub_pos.mpr hAB)] using H
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have H := (h1.add ((ha.sub hb).div hs (ne_of_gt (sub_pos.mpr hAB)))).div_const 2
  simpa only [softWeight,softSlope,Pi.div_apply,div_self (ne_of_gt (sub_pos.mpr hAB)),one_add_one_eq_two,div_self (by norm_num : (2:ℝ)≠0)] using H

lemma softWeight_tendsto_of_gt {e a b : ℕ → ℝ} {A B : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hAB : A<B) : Tendsto (fun n => softWeight (e n) (a n-b n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => softAbs (e n) (a n-b n)) atTop (𝓝 (B-A)) := by
    have H := (((ha.sub hb).pow 2).add (he.pow 2)).sqrt
    simpa only [softAbs,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_sq_eq_abs,
      abs_of_neg (sub_neg.mpr hAB),neg_sub] using H
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have H := (h1.add ((ha.sub hb).div hs (ne_of_gt (sub_pos.mpr hAB)))).div_const 2
  have hr : (A-B)/(B-A)= -1 := by rw [show A-B= -(B-A) by ring,neg_div,div_self (ne_of_gt (sub_pos.mpr hAB))]
  simpa only [softWeight,softSlope,Pi.div_apply,hr,add_neg_cancel,zero_div] using H

lemma convex_pair_bounds {p u v : ℝ} (hp : 0≤ p) (hp1 : p≤ 1) :
    min u v≤ p*u+(1-p)*v ∧ p*u+(1-p)*v≤ max u v := by
  by_cases h : u≤ v
  · rw [min_eq_left h,max_eq_right h]
    constructor <;> nlinarith [mul_nonneg hp (sub_nonneg.mpr h),mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr h)]
  · have h := le_of_not_ge h
    rw [min_eq_right h,max_eq_left h]
    constructor <;> nlinarith [mul_nonneg hp (sub_nonneg.mpr h),mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr h)]

lemma softWeight_response_tendsto {e a b q r : ℕ → ℝ} {A B Q R : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hep : ∀ n,0<e n)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hq : Tendsto q atTop (𝓝 Q)) (hr : Tendsto r atTop (𝓝 R))
    (htie : A=B → Q=R) :
    Tendsto (fun n => softWeight (e n) (a n-b n)*q n+
      (1-softWeight (e n) (a n-b n))*r n) atTop (𝓝 (if B≤ A then Q else R)) := by
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  rcases lt_trichotomy A B with h|h|h
  · rw [ite_eq_right (not_le.mpr h)]
    have hw := softWeight_tendsto_of_gt he ha hb h
    simpa using (hw.mul hq).add ((h1.sub hw).mul hr)
  · have hQR := htie h
    rw [ite_eq_left h.ge,hQR]
    rw [hQR] at hq
    apply (show Tendsto (fun n => min (q n) (r n)) atTop (𝓝 R) by simpa using hq.min hr).squeeze
      (show Tendsto (fun n => max (q n) (r n)) atTop (𝓝 R) by simpa using hq.max hr)
    · intro n; exact (convex_pair_bounds (softWeight_bounds (hep n) _).1 (softWeight_bounds (hep n) _).2).1
    · intro n; exact (convex_pair_bounds (softWeight_bounds (hep n) _).1 (softWeight_bounds (hep n) _).2).2
  · rw [ite_eq_left h.le]
    have hw := softWeight_tendsto_of_lt he ha hb h
    simpa using (hw.mul hq).add ((h1.sub hw).mul hr)

end NeutralAtom

end

end OAI
