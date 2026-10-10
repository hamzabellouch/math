import Mathlib
import OAI.Probability.ThreeStateClauses.RadialAlgebra

namespace OAI

/-! Radial Bounds. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
namespace ThreeState.TreeClauses.Radial

def f₀ (r : ℝ) : ℝ := 480*r^4 - 842*r^3 - 117*r^2 + 445*r + 160

def f₁ (r : ℝ) : ℝ :=
  336*r^6 - 1008*r^5 + 1096*r^4 - 896*r^3 + 63*r^2 + 685*r + 240

def f₂ (r : ℝ) : ℝ := 440*r^4 - 1104*r^3 + 368*r^2 + 413*r + 210

lemma f₀_certificate (p : ℝ) (hp : 0 ≤ p) :
    4*(1+p)^4 * f₀ ((p-1/2)/(1+p)) =
      504*p^4 + 4386*p^3 + 12267*p^2 - 1161*p + 174 := by
  have h : 1+p ≠ 0 := by positivity
  dsimp [f₀]; field_simp; ring

lemma f₁_certificate (p : ℝ) (hp : 0 ≤ p) :
    4*(1+p)^6 * f₁ ((p-1/2)/(1+p)) =
      2064*p^6 + 15486*p^5 + 36669*p^4 + 31368*p^3 +
        20184*p^2 - 2724*p + 522 := by
  have h : 1+p ≠ 0 := by positivity
  dsimp [f₁]; field_simp; ring

lemma f₂_certificate (p : ℝ) (hp : 0 ≤ p) :
    4*(1+p)^4 * f₂ ((p-1/2)/(1+p)) =
      1308*p^4 + 7650*p^3 + 12366*p^2 - 1842*p + 1044 := by
  have h : 1+p ≠ 0 := by positivity
  dsimp [f₂]; field_simp; ring

lemma f_positive (r : ℝ) (hr₀ : -(1/2:ℝ) ≤ r) (hr₁ : r ≤ 1) :
    0 < f₀ r ∧ 0 < f₁ r ∧ 0 < f₂ r := by
  rcases hr₁.eq_or_lt with hr | hr
  · subst r; norm_num [f₀, f₁, f₂]
  let p := (r+1/2)/(1-r)
  have hp : 0 ≤ p := div_nonneg (by linarith) (by linarith)
  have hp1 : 0 < 1+p := by positivity
  have hrp : r = (p-1/2)/(1+p) := by
    have heq : p*(1-r) = r+1/2 := div_mul_cancel₀ _ (by linarith : 1-r ≠ 0)
    apply (eq_div_iff (ne_of_gt hp1)).2
    nlinarith [heq]
  have h₀ : 0 < 12267*p^2 - 1161*p + 174 := by
    nlinarith [sq_nonneg (p - (1161 / (2*12267) : ℝ))]
  have h₁ : 0 < 20184*p^2 - 2724*p + 522 := by
    nlinarith [sq_nonneg (p - (2724 / (2*20184) : ℝ))]
  have h₂ : 0 < 12366*p^2 - 1842*p + 1044 := by
    nlinarith [sq_nonneg (p - (1842 / (2*12366) : ℝ))]
  rw [hrp]
  constructor
  · have ht : 0 ≤ 504*p^4 + 4386*p^3 := by positivity
    have hc := f₀_certificate p hp
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*(1+p)^4)).1 (by linarith)
  constructor
  · have ht : 0 ≤ 2064*p^6 + 15486*p^5 + 36669*p^4 + 31368*p^3 := by positivity
    have hc := f₁_certificate p hp
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*(1+p)^6)).1 (by linarith)
  · have ht : 0 ≤ 1308*p^4 + 7650*p^3 := by positivity
    have hc := f₂_certificate p hp
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*(1+p)^4)).1 (by linarith)

def a₀ (r : ℝ) : ℝ := (1-r)^3*(3-2*r)^2*(10*r^2+r+1)

def a₁ (r : ℝ) : ℝ := 2*(1-r)^3*(3-2*r)*(9+5*r+20*r^2-4*r^3)

def a₂ (r : ℝ) : ℝ := 48*(1-r)^3

def b₀ (r : ℝ) : ℝ := r^2*(1-r)^3*(3-2*r)^3*f₀ r

def b₁ (r : ℝ) : ℝ := (1-r)^3*(3-2*r)^2*f₁ r

def b₂ (r : ℝ) : ℝ := 2*(1-r)^3*(3-2*r)*f₂ r

def b₃ (r : ℝ) : ℝ := 24*(1-r)^3*(25-4*r^2-10*r)

lemma a_nonneg (r : ℝ) (hr₀ : -(1/2:ℝ) ≤ r) (hr₁ : r ≤ 1) :
    0 ≤ a₀ r ∧ 0 ≤ a₁ r ∧ 0 ≤ a₂ r := by
  have h1 : 0 ≤ 1-r := by linarith
  have h3 : 0 ≤ 3-2*r := by linarith
  have hq : 0 ≤ 10*r^2+r+1 := by nlinarith [sq_nonneg (r+1/20)]
  have hc : 0 ≤ 9+5*r+20*r^2-4*r^3 := by
    have h : 0 ≤ r^2*(20-4*r) := mul_nonneg (sq_nonneg r) (by linarith)
    nlinarith
  dsimp [a₀, a₁, a₂]
  exact ⟨by positivity, by positivity, by positivity⟩

lemma b_nonneg (r : ℝ) (hr₀ : -(1/2:ℝ) ≤ r) (hr₁ : r ≤ 1) :
    0 ≤ b₀ r ∧ 0 ≤ b₁ r ∧ 0 ≤ b₂ r ∧ 0 ≤ b₃ r := by
  have h1 : 0 ≤ 1-r := by linarith
  have h3 : 0 ≤ 3-2*r := by linarith
  obtain ⟨hf₀, hf₁, hf₂⟩ := f_positive r hr₀ hr₁
  have hq : 0 ≤ 25-4*r^2-10*r := by
    have h : 0 ≤ (1-r)*(r+1/2) := mul_nonneg h1 (by linarith)
    nlinarith
  dsimp [b₀, b₁, b₂, b₃]
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

def normalizedA (x r : ℝ) : ℝ :=
  (3-6*r)*x^2 + (12-28*r+26*r^2-4*r^3)*x + 1-2*r-2*r^2

def normalizedL (x r : ℝ) : ℝ :=
  (1500-3093*r+2114*r^2-480*r^3)*x^3 +
  (168*r^4-756*r^3+710*r^2+736*r-1020)*x^2 +
  (240-35*r+48*r^2-52*r^3)*x - 80*r^2

lemma normalizeA (x r : ℝ) : polyA x (r*x) = x^2*normalizedA x r := by
  dsimp [polyA, normalizedA]; ring

lemma normalizeL (x r : ℝ) : polyL x (r*x) = x^2*normalizedL x r := by
  dsimp [polyL, normalizedL]; ring

def paramX (r z : ℝ) : ℝ := (r^2+z/(3-2*r))/(1+z)

lemma a_certificate (r z : ℝ) (hr : r ≤ 1) (hz : 0 ≤ z) :
    (1+z)^2*(3-2*r)^2*normalizedA (paramX r z) r =
      a₀ r + a₁ r*z + a₂ r*z^2 := by
  have h1 : 1+z ≠ 0 := by positivity
  have h3 : 3-2*r ≠ 0 := by linarith
  dsimp [paramX, normalizedA, a₀, a₁, a₂]
  field_simp
  ring

lemma b_certificate (r z : ℝ) (hr : r ≤ 1) (hz : 0 ≤ z) :
    (1+z)^3*(3-2*r)^3*normalizedL (paramX r z) r =
      b₀ r + b₁ r*z + b₂ r*z^2 + b₃ r*z^3 := by
  have h1 : 1+z ≠ 0 := by positivity
  have h3 : 3-2*r ≠ 0 := by linarith
  dsimp [paramX, normalizedL, b₀, b₁, b₂, b₃, f₀, f₁, f₂]
  field_simp
  ring

lemma param_polynomial_nonneg (r z : ℝ) (hr₀ : -(1/2:ℝ) ≤ r)
    (hr₁ : r ≤ 1) (hz : 0 ≤ z) :
    0 ≤ polyA (paramX r z) (r*paramX r z) ∧
    0 ≤ polyL (paramX r z) (r*paramX r z) := by
  have h1 : 0 < 1+z := by positivity
  have h3 : 0 < 3-2*r := by linarith
  obtain ⟨ha₀, ha₁, ha₂⟩ := a_nonneg r hr₀ hr₁
  obtain ⟨hb₀, hb₁, hb₂, hb₃⟩ := b_nonneg r hr₀ hr₁
  constructor
  · rw [normalizeA]
    apply mul_nonneg (sq_nonneg _)
    apply (nonneg_of_mul_nonneg_left _ (by positivity : 0 < (1+z)^2*(3-2*r)^2))
    rw [mul_comm, a_certificate r z hr₁ hz]
    positivity
  · rw [normalizeL]
    apply mul_nonneg (sq_nonneg _)
    apply (nonneg_of_mul_nonneg_left _ (by positivity : 0 < (1+z)^3*(3-2*r)^3))
    rw [mul_comm, b_certificate r z hr₁ hz]
    positivity

lemma domain_parametrization {x y : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1)
    (hxy : y^2 ≤ x^3) (hD : 0 < 1-3*x+2*y) :
    ∃ r z : ℝ, -(1/2:ℝ) ≤ r ∧ r < 1 ∧ 0 ≤ z ∧
      x = paramX r z ∧ y = r*x := by
  let r := y/x
  have hyr : y = r*x := by dsimp [r]; field_simp
  have hrx : r^2 ≤ x := by
    dsimp [r]; rw [div_pow]
    apply (div_le_iff₀ (pow_pos hx₀ 2)).2
    nlinarith
  have hr₁ : r < 1 := by nlinarith [sq_nonneg (r-1)]
  have h3 : 0 < 3-2*r := by linarith
  have hD' : 0 < 1-(3-2*r)*x := by rw [hyr] at hD; nlinarith
  have hfactor : 0 < (1-r)^2*(2*r+1) := by
    nlinarith [mul_nonneg h3.le (sub_nonneg.mpr hrx)]
  have hr₀ : -(1/2:ℝ) ≤ r := by
    have hsq : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
    have := (mul_pos_iff_of_pos_left hsq).1 hfactor
    linarith
  have hden : 0 < 1/(3-2*r)-x := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ h3).2
    nlinarith
  let z := (x-r^2)/(1/(3-2*r)-x)
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hrx) hden.le
  have hz1 : 0 < 1+z := by positivity
  have hzEq : z*(1/(3-2*r)-x) = x-r^2 := div_mul_cancel₀ _ (ne_of_gt hden)
  refine ⟨r, z, hr₀, hr₁, hz, ?_, hyr⟩
  dsimp only [paramX]
  apply (eq_div_iff (ne_of_gt hz1)).2
  simp only [div_eq_mul_inv, one_mul] at hzEq ⊢
  nlinarith

lemma polyN_one_nonneg {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hxy : y^2 ≤ x^3) : 0 ≤ polyN x y 1 := by
  have hx3 : x^3 ≤ x^2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx₁)]
  have hyx : y ≤ x := by nlinarith [sq_nonneg (y-x)]
  have hlast : 0 ≤ x^2+x-2*y := by
    by_contra h
    have hminus : 0 < 2*y-(x^2+x) := by linarith
    have hplus : 0 < 2*y+(x^2+x) := by nlinarith
    have hp := mul_pos hminus hplus
    have hsq : 0 ≤ x^2*(x-1)^2 := by positivity
    nlinarith
  rw [polyN_one]
  have hfirst : 0 ≤ x-y := by linarith
  have hsecond : 0 ≤ 9*x-10*y+1 := by linarith
  positivity

lemma polynomial_goal {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hxy : y^2 ≤ x^3) (hD : 0 < 1-3*x+2*y) :
    0 ≤ polyN x y 0 ∧ 0 ≤ polyN x y 1 ∧ 0 ≤ polyL x y := by
  rcases eq_or_lt_of_le hx₀ with hx | hx
  · have hy : y = 0 := by rw [← hx] at hxy; nlinarith [sq_nonneg y]
    rw [← hx, hy]; norm_num [polyN, polyA, polyC, polyL]
  · obtain ⟨r,z,hr₀,hr₁,hz,hxp,hyr⟩ := domain_parametrization hx hx₁ hxy hD
    have hs := param_polynomial_nonneg r z hr₀ hr₁.le hz
    rw [← hxp, ← hyr] at hs
    refine ⟨?_, polyN_one_nonneg hx₀ hx₁.le hxy, hs.2⟩
    dsimp only [polyN]
    nlinarith [hs.1]

lemma polyN_nonneg {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1)
    (hxy : y^2 ≤ x^3) (hD : 0 < 1-3*x+2*y)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ polyN x y t := by
  obtain ⟨h0,h1,_⟩ := polynomial_goal hx₀ hx₁ hxy hD
  rw [polyN_affine]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) h0) (mul_nonneg ht.1 h1)

end ThreeState.TreeClauses.Radial

end 

noncomputable section
open MeasureTheory Set
open scoped Interval
namespace ThreeState.TreeClauses.Radial

def denom (v : Vec) (t : ℝ) : ℝ := 1 - 3*t^2*momentX v + 2*t^3*momentY v

def kpoly (v : Vec) (t : ℝ) : Vec := fun i ↦ v i - t * (v i^2 - 2*momentX v)

def invMoment (m : Vec) (j : ℕ) : ℝ := avg (fun i ↦ (m i)⁻¹ ^ j)

def logInvMoment (m : Vec) (j : ℕ) : ℝ :=
  avg (fun i ↦ logCentered m i * (m i)⁻¹ ^ j)

def logMoment (m : Vec) : ℝ := avg (fun i ↦ m i * logCentered m i)

def radialG (m : Vec) : ℝ :=
  6 - 12 * invMoment m 1 + 8 * invMoment m 2 - 2 * invMoment m 3 +
  (4/5) * (logInvMoment m 2 - 3*logInvMoment m 1 +
    (2*invMoment m 3 - 3*invMoment m 2)*logMoment m +
    3*(invMoment m 1-1)*(invMoment m 2-invMoment m 1))

lemma edge_pos {m : Vec} (hm : PositiveMessage m) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (i : Fin 3) : 0 < 1+t*centered m i := by
  by_cases h : t = 0
  · subst t; norm_num
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have := mul_pos ht0 (hm.1 i)
    dsimp only [centered]; nlinarith [ht.2]

lemma denom_pos {m : Vec} (hm : PositiveMessage m) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 < denom (centered m) t := denominator_pos hm t ht

lemma rational_identity {v : Vec} (hv : avg v = 0) (t : ℝ) (i : Fin 3)
    (hi : 1+t*v i ≠ 0) (hD : denom v t ≠ 0) :
    v i / (1+t*v i) = (v i - t*v i^2 + 2*t^2*momentY v) / denom v t := by
  apply (div_eq_div_iff hi hD).2
  dsimp only [denom]
  linear_combination t^2 * cubic hv i

lemma rational_centered {v : Vec} (hv : avg v = 0) (t : ℝ)
    (hi : ∀ i, 1+t*v i ≠ 0) (hD : denom v t ≠ 0) (i : Fin 3) :
    v i / (1+t*v i) - avg (fun j ↦ v j / (1+t*v j)) = kpoly v t i / denom v t := by
  simp_rw [rational_identity hv t _ (hi _) hD]
  dsimp only [avg, kpoly, momentX, momentY]
  have hs := third_eq hv
  field_simp
  rw [hs]
  ring

lemma hasDerivAt_log_edge {v : Vec} {t : ℝ} (i : Fin 3) (hi : 1+t*v i ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ Real.log (1+s*v i)) (v i/(1+t*v i)) t := by
  convert ((hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).mul_const (v i))).log hi using 1 <;> simp

lemma integral_log_edge {m : Vec} (hm : PositiveMessage m) (i : Fin 3) :
    (∫ t in (0:ℝ)..1, centered m i / (1+t*centered m i)) = Real.log (m i) := by
  have hc : ContinuousOn (fun t : ℝ ↦ centered m i / (1+t*centered m i)) (Icc 0 1) := by
    apply continuousOn_const.div (by fun_prop)
    intro t ht; exact ne_of_gt (edge_pos hm ht i)
  have hint : IntervalIntegrable (fun t : ℝ ↦ centered m i / (1+t*centered m i)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t ∈ uIcc (0:ℝ) 1) ↦
      hasDerivAt_log_edge i (ne_of_gt (edge_pos hm (by simpa using ht) i))) hint
  simpa [centered] using h

lemma integral_avg {f : ℝ → Vec}
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t i) volume (0:ℝ) 1) :
    (∫ t in (0:ℝ)..1, avg (f t)) = avg (fun i ↦ ∫ t in (0:ℝ)..1, f t i) := by
  simp only [avg, intervalIntegral.integral_div,
    intervalIntegral.integral_add (hf 0) (hf 1),
    intervalIntegral.integral_add ((hf 0).add (hf 1)) (hf 2)]

lemma integral_k {m : Vec} (hm : PositiveMessage m) (i : Fin 3) :
    (∫ t in (0:ℝ)..1, kpoly (centered m) t i / denom (centered m) t) = logCentered m i := by
  have hint (j : Fin 3) : IntervalIntegrable
      (fun t : ℝ ↦ centered m j/(1+t*centered m j)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact continuousOn_const.div (by fun_prop) (fun t ht ↦ ne_of_gt (edge_pos hm ht j))
  have havg : IntervalIntegrable
      (fun t : ℝ ↦ avg (fun j ↦ centered m j/(1+t*centered m j))) volume 0 1 := by
    exact (((hint 0).add (hint 1)).add (hint 2)).div_const 3
  calc
    _ = ∫ t in (0:ℝ)..1, centered m i/(1+t*centered m i) -
        avg (fun j ↦ centered m j/(1+t*centered m j)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      symm
      exact rational_centered (avg_centered hm) t
        (fun j ↦ ne_of_gt (edge_pos hm (by simpa using ht) j))
        (ne_of_gt (denom_pos hm (by simpa using ht))) i
    _ = _ := by
      rw [intervalIntegral.integral_sub (hint i) havg, integral_log_edge hm,
        integral_avg hint]
      simp only [integral_log_edge hm, logCentered, logAverage]

lemma avg_div (v : Vec) (a : ℝ) : avg (fun i ↦ v i / a) = avg v / a := by
  simp only [avg]; ring

lemma avg_logCentered (m : Vec) : avg (logCentered m) = 0 := by
  simp only [logCentered, logAverage, avg]; ring

lemma h_inverse {m : Vec} (hm : PositiveMessage m) (i : Fin 3) :
    (m i)⁻¹ = hpoly (centered m) i / denom (centered m) 1 := by
  have hc := cubic (avg_centered hm) i
  have hD := ne_of_gt (denom_pos hm (by norm_num : (1:ℝ) ∈ Icc 0 1))
  apply (eq_div_iff hD).2
  apply (mul_left_cancel₀ (ne_of_gt (hm.1 i)))
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hm.1 i)), one_mul]
  dsimp only [denom, hpoly, centered] at *
  norm_num only [one_pow, mul_one, one_mul]
  linear_combination -hc

def polynomialR (v : Vec) : ℝ :=
  (6-12*momentX v^2)*denom v 1^3 - 12*Hpoly 1 v*denom v 1^2 +
  8*Hpoly 2 v*denom v 1 - 2*Hpoly 3 v +
  (12/5)*(Hpoly 1 v-denom v 1)*(Hpoly 2 v-Hpoly 1 v*denom v 1)

def logWeight (v : Vec) : Vec := fun i ↦
  hpoly v i^2*denom v 1 - 3*hpoly v i*denom v 1^2 +
  (2*Hpoly 3 v-3*Hpoly 2 v*denom v 1)*v i

lemma polynomialN_representation {v : Vec} (hv : avg v = 0) (t : ℝ) :
    (4/5)*avg (fun i ↦ kpoly v t i * logWeight v i) =
      polyN (momentX v) (momentY v) t := by
  simp only [logWeight, Hpoly, kpoly, hpoly, denom, polyN, polyA, polyC,
    momentX, momentY, avg]
  rw [third_eq hv]
  ring

lemma G_algebra {m : Vec} (hm : PositiveMessage m) :
    denom (centered m) 1^3 * (radialG m-12*momentX (centered m)^2) =
      polynomialR (centered m) + (4/5)*avg (fun i ↦ logCentered m i * logWeight (centered m) i) := by
  have hD := ne_of_gt (denom_pos hm (by norm_num : (1:ℝ) ∈ Icc 0 1))
  simp only [radialG, invMoment, logInvMoment, logMoment]
  simp_rw [h_inverse hm]
  simp only [polynomialR, logWeight, Hpoly, avg, logCentered, logAverage, centered]
  field_simp
  ring

lemma integrable_k {m : Vec} (hm : PositiveMessage m) (i : Fin 3) :
    IntervalIntegrable (fun t ↦ kpoly (centered m) t i / denom (centered m) t) volume (0:ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply ContinuousOn.div (by unfold kpoly; fun_prop) (by unfold denom; fun_prop)
  intro t ht; exact ne_of_gt (denom_pos hm ht)

lemma integral_N {m : Vec} (hm : PositiveMessage m) :
    (∫ t in (0:ℝ)..1, polyN (momentX (centered m)) (momentY (centered m)) t /
      denom (centered m) t) =
      (4/5)*avg (fun i ↦ logCentered m i * logWeight (centered m) i) := by
  have heq (t : ℝ) : polyN (momentX (centered m)) (momentY (centered m)) t /
      denom (centered m) t = (4/5)*avg (fun i ↦
        (kpoly (centered m) t i / denom (centered m) t) * logWeight (centered m) i) := by
    rw [← polynomialN_representation (avg_centered hm)]
    simp only [avg]; ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul,
    integral_avg (fun i ↦ (integrable_k hm i).mul_const _)]
  simp only [intervalIntegral.integral_mul_const, integral_k hm]

lemma RN_representation {m : Vec} (hm : PositiveMessage m) :
    denom (centered m) 1^3 * (radialG m-12*momentX (centered m)^2) =
      polynomialR (centered m) +
      (∫ t in (0:ℝ)..1, polyN (momentX (centered m)) (momentY (centered m)) t /
        denom (centered m) t) := by rw [integral_N hm, G_algebra hm]

lemma polynomial_integral (x y : ℝ) :
    (∫ t in (0:ℝ)..1, polyN x y t * (2-(1-3*t^2*x+2*t^3*y))) =
      (24/5)*(polyA x y*(1+x-y/2)+polyC x y*(1/2+3*x/4-2*y/5)) := by
  simp only [polyN]
  conv_lhs => arg 1; ext t; ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_pow, intervalIntegral.integral_const]
  norm_num
  ring

lemma L_representation {v : Vec} (hv : avg v = 0) :
    polynomialR v + (∫ t in (0:ℝ)..1, polyN (momentX v) (momentY v) t * (2-denom v t)) =
      (6/25)*polyL (momentX v) (momentY v) := by
  simp only [denom]
  rw [polynomial_integral]
  simp only [polynomialR, denom, Hpoly_one hv, Hpoly_two hv, Hpoly_three hv,
    polyL, polyA, polyC]
  ring

theorem radialG_bound {m : Vec} (hm : PositiveMessage m) :
    12*momentX (centered m)^2 ≤ radialG m := by
  let v := centered m
  have hx₀ := momentX_nonneg v
  have hx₁ := momentX_lt_one hm
  have hxy := moment_discriminant (avg_centered hm)
  have hD : 0 < 1-3*momentX v+2*momentY v := by
    simpa [v, denom] using denom_pos hm (by norm_num : (1:ℝ) ∈ Icc 0 1)
  have hN (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ polyN (momentX v) (momentY v) t :=
    polyN_nonneg hx₀ hx₁ hxy hD ht
  have hL := (polynomial_goal hx₀ hx₁ hxy hD).2.2
  have hcN : Continuous (fun t : ℝ ↦ polyN (momentX v) (momentY v) t) := by
    unfold polyN; fun_prop
  have hcl : Continuous (fun t : ℝ ↦ polyN (momentX v) (momentY v) t * (2-denom v t)) := by
    unfold denom; fun_prop
  have hcr : ContinuousOn (fun t : ℝ ↦ polyN (momentX v) (momentY v) t / denom v t)
      (Icc 0 1) := by
    exact hcN.continuousOn.div (by unfold denom; fun_prop)
      (fun t ht ↦ ne_of_gt (denom_pos hm ht))
  have hir : IntervalIntegrable (fun t : ℝ ↦ polyN (momentX v) (momentY v) t / denom v t) volume 0 1 :=
    hcr.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
  have hi : (∫ t in (0:ℝ)..1, polyN (momentX v) (momentY v) t * (2-denom v t)) ≤
      (∫ t in (0:ℝ)..1, polyN (momentX v) (momentY v) t / denom v t) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hcl.intervalIntegrable _ _) hir
    intro t ht
    have hd := denom_pos hm ht
    have hh : 2-denom v t ≤ 1/denom v t := by
      apply (le_div_iff₀ hd).2
      nlinarith [sq_nonneg (1-denom v t)]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hh (hN t ht)
  have hp : 0 ≤ denom v 1^3 * (radialG m-12*momentX v^2) := by
    rw [RN_representation hm]
    have he := L_representation (avg_centered hm)
    dsimp only [v] at hi hL ⊢
    linarith
  have hd : 0 < denom v 1^3 := pow_pos (denom_pos hm (by norm_num)) 3
  have := (mul_nonneg_iff_of_pos_left hd).1 hp
  linarith

end ThreeState.TreeClauses.Radial

end

end OAI
