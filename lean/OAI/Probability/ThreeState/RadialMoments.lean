import Mathlib

namespace OAI

/-! Three-coordinate moment identities and positive radial polynomials. -/

namespace ThreeState.Radial

noncomputable def f0 (r : ℝ) : ℝ := 480*r^4-842*r^3-117*r^2+445*r+160
noncomputable def f1 (r : ℝ) : ℝ :=
  336*r^6-1008*r^5+1096*r^4-896*r^3+63*r^2+685*r+240
noncomputable def f2 (r : ℝ) : ℝ := 440*r^4-1104*r^3+368*r^2+413*r+210

lemma tail0_pos (p : ℝ) : 0 < 12267*p^2-1161*p+174 := by
  nlinarith [sq_nonneg (24534*p-1161)]
lemma tail1_pos (p : ℝ) : 0 < 20184*p^2-2724*p+522 := by
  nlinarith [sq_nonneg (40368*p-2724)]
lemma tail2_pos (p : ℝ) : 0 < 12366*p^2-1842*p+1044 := by
  nlinarith [sq_nonneg (24732*p-1842)]

lemma transform_f0 (p : ℝ) (hp : 1+p ≠ 0) :
    4*(1+p)^4*f0 ((p-1/2)/(1+p)) =
      504*p^4+4386*p^3+12267*p^2-1161*p+174 := by
  unfold f0
  field_simp
  ring

lemma transform_f1 (p : ℝ) (hp : 1+p ≠ 0) :
    4*(1+p)^6*f1 ((p-1/2)/(1+p)) =
      2064*p^6+15486*p^5+36669*p^4+31368*p^3+20184*p^2-2724*p+522 := by
  unfold f1
  field_simp
  ring

lemma transform_f2 (p : ℝ) (hp : 1+p ≠ 0) :
    4*(1+p)^4*f2 ((p-1/2)/(1+p)) =
      1308*p^4+7650*p^3+12366*p^2-1842*p+1044 := by
  unfold f2
  field_simp
  ring

lemma f0_pos (r : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1) : 0 < f0 r := by
  let p := (r+1/2)/(1-r)
  have hp : 0 ≤ p := div_nonneg (by linarith) (by linarith)
  have hden : 1+p ≠ 0 := ne_of_gt (by linarith)
  have hr : (p-1/2)/(1+p) = r := by
    apply (div_eq_iff hden).2
    dsimp [p]
    have h1 : 1-r ≠ 0 := by linarith
    field_simp
    ring
  have ht := transform_f0 p hden
  rw [hr] at ht
  have hrest : 0 ≤ 504*p^4+4386*p^3 := by positivity
  have hmul : 0 < 4*(1+p)^4 * f0 r := by linarith [tail0_pos p]
  exact pos_of_mul_pos_right hmul (by positivity)

lemma f1_pos (r : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1) : 0 < f1 r := by
  let p := (r+1/2)/(1-r)
  have hp : 0 ≤ p := div_nonneg (by linarith) (by linarith)
  have hden : 1+p ≠ 0 := ne_of_gt (by linarith)
  have hr : (p-1/2)/(1+p) = r := by
    apply (div_eq_iff hden).2
    dsimp [p]
    have h1 : 1-r ≠ 0 := by linarith
    field_simp
    ring
  have ht := transform_f1 p hden
  rw [hr] at ht
  have hrest : 0 ≤ 2064*p^6+15486*p^5+36669*p^4+31368*p^3 := by positivity
  have hmul : 0 < 4*(1+p)^6 * f1 r := by linarith [tail1_pos p]
  exact pos_of_mul_pos_right hmul (by positivity)

lemma f2_pos (r : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1) : 0 < f2 r := by
  let p := (r+1/2)/(1-r)
  have hp : 0 ≤ p := div_nonneg (by linarith) (by linarith)
  have hden : 1+p ≠ 0 := ne_of_gt (by linarith)
  have hr : (p-1/2)/(1+p) = r := by
    apply (div_eq_iff hden).2
    dsimp [p]
    have h1 : 1-r ≠ 0 := by linarith
    field_simp
    ring
  have ht := transform_f2 p hden
  rw [hr] at ht
  have hrest : 0 ≤ 1308*p^4+7650*p^3 := by positivity
  have hmul : 0 < 4*(1+p)^4 * f2 r := by linarith [tail2_pos p]
  exact pos_of_mul_pos_right hmul (by positivity)

noncomputable def A (x y : ℝ) : ℝ :=
  3*x^4+12*x^3+x^2+(-6*x^3-28*x^2-2*x)*y+(26*x-2)*y^2-4*y^3
noncomputable def C (x y : ℝ) : ℝ :=
  6*x^4-2*x^3+(-13*x^3-10*x^2-x)*y+(10*x^2+22*x+4)*y^2-16*y^3
noncomputable def Lscaled (x y : ℝ) : ℝ :=
  1500*x^5-1020*x^4+240*x^3+168*y^4+(-480*x^2-756*x-52)*y^3+
  (2114*x^3+710*x^2+48*x-80)*y^2+(-3093*x^4+736*x^3-35*x^2)*y

lemma N1_factor (x y : ℝ) :
    A x y + C x y = (x-y)*(9*x-10*y+1)*(x^2+x-2*y) := by
  unfold A C
  ring

noncomputable def xa (r z : ℝ) : ℝ := (r^2+z/(3-2*r))/(1+z)
noncomputable def a0 (r : ℝ) : ℝ := (1-r)^3*(3-2*r)^2*(10*r^2+r+1)
noncomputable def a1 (r : ℝ) : ℝ := 2*(1-r)^3*(3-2*r)*(9+5*r+20*r^2-4*r^3)
noncomputable def a2 (r : ℝ) : ℝ := 48*(1-r)^3
noncomputable def b0 (r : ℝ) : ℝ := r^2*(1-r)^3*(3-2*r)^3*f0 r
noncomputable def b1 (r : ℝ) : ℝ := (1-r)^3*(3-2*r)^2*f1 r
noncomputable def b2 (r : ℝ) : ℝ := 2*(1-r)^3*(3-2*r)*f2 r
noncomputable def b3 (r : ℝ) : ℝ := 24*(1-r)^3*(25-4*r^2-10*r)

lemma a_nonneg (r : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1) :
    0 ≤ a0 r ∧ 0 ≤ a1 r ∧ 0 ≤ a2 r := by
  have h1 : 0 ≤ 1-r := by linarith
  have h2 : 0 ≤ 3-2*r := by linarith
  have h3 : 0 ≤ 10*r^2+r+1 := by nlinarith [sq_nonneg (20*r+1)]
  have h4a : 0 ≤ r^2*(20-4*r) := mul_nonneg (sq_nonneg _) (by linarith)
  have h4 : 0 ≤ 9+5*r+20*r^2-4*r^3 := by nlinarith
  dsimp [a0, a1, a2]
  exact ⟨by positivity, by positivity, by positivity⟩

lemma b_nonneg (r : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1) :
    0 ≤ b0 r ∧ 0 ≤ b1 r ∧ 0 ≤ b2 r ∧ 0 ≤ b3 r := by
  have h1 : 0 ≤ 1-r := by linarith
  have h2 : 0 ≤ 3-2*r := by linarith
  have h3a : 0 ≤ (1-r)*(4*r+14) := mul_nonneg h1 (by linarith)
  have h3 : 0 ≤ 25-4*r^2-10*r := by nlinarith
  have hf0 := (f0_pos r hl hu).le
  have hf1 := (f1_pos r hl hu).le
  have hf2 := (f2_pos r hl hu).le
  dsimp [b0, b1, b2, b3]
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

lemma A_certificate (r z : ℝ) (hr : 3-2*r ≠ 0) (hz : 1+z ≠ 0) :
    (1+z)^2*(3-2*r)^2 * A (xa r z) (r*xa r z) =
      (xa r z)^2*(a0 r+a1 r*z+a2 r*z^2) := by
  dsimp [A, xa, a0, a1, a2]
  field_simp
  ring

lemma L_certificate (r z : ℝ) (hr : 3-2*r ≠ 0) (hz : 1+z ≠ 0) :
    (1+z)^3*(3-2*r)^3 * Lscaled (xa r z) (r*xa r z) =
      (xa r z)^2*(b0 r+b1 r*z+b2 r*z^2+b3 r*z^3) := by
  dsimp [Lscaled, xa, b0, b1, b2, b3, f0, f1, f2]
  field_simp
  ring

lemma A_nonneg_param (r z : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1)
    (hz : 0 ≤ z) : 0 ≤ A (xa r z) (r*xa r z) := by
  have h1 : 0 < 1+z := by linarith
  have h2 : 0 < 3-2*r := by linarith
  obtain ⟨h0, ha1, ha2⟩ := a_nonneg r hl hu
  have hrhs : 0 ≤ (xa r z)^2*(a0 r+a1 r*z+a2 r*z^2) := by positivity
  rw [← A_certificate r z (ne_of_gt h2) (ne_of_gt h1)] at hrhs
  exact nonneg_of_mul_nonneg_right hrhs (by positivity)

lemma L_nonneg_param (r z : ℝ) (hl : -(1/2 : ℝ) ≤ r) (hu : r < 1)
    (hz : 0 ≤ z) : 0 ≤ Lscaled (xa r z) (r*xa r z) := by
  have h1 : 0 < 1+z := by linarith
  have h2 : 0 < 3-2*r := by linarith
  obtain ⟨h0, hb1, hb2, hb3⟩ := b_nonneg r hl hu
  have hrhs : 0 ≤ (xa r z)^2*(b0 r+b1 r*z+b2 r*z^2+b3 r*z^3) := by positivity
  rw [← L_certificate r z (ne_of_gt h2) (ne_of_gt h1)] at hrhs
  exact nonneg_of_mul_nonneg_right hrhs (by positivity)

lemma physical_parameterization (x y : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (hdisc : y^2 ≤ x^3) (hD : 0 < 1-3*x+2*y) :
    ∃ r z : ℝ, -(1/2 : ℝ) ≤ r ∧ r < 1 ∧ 0 ≤ z ∧
      x = xa r z ∧ y = r * x := by
  let r := y/x
  have hylt : y < x := by
    nlinarith [mul_pos (sq_pos_of_pos hx) (sub_pos.mpr hx1)]
  have hr1 : r < 1 := (div_lt_one hx).2 hylt
  have hyr : y = r*x := by dsimp [r]; field_simp
  have hrsq : r^2 ≤ x := by
    dsimp [r]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hx)).2
    nlinarith
  have hden : 0 < 3-2*r := by linarith
  have hupper : x < 1/(3-2*r) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [hD]
  have hdsq : r^2*(3-2*r) < 1 := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hrsq hden.le) ((lt_div_iff₀ hden).1 hupper)
  have hpos : 0 < (1-r)^2*(1+2*r) := by nlinarith
  have hrlo : -(1/2 : ℝ) ≤ r := by
    have := pos_of_mul_pos_right hpos (sq_nonneg (1-r))
    linarith
  let z := (x-r^2)/(1/(3-2*r)-x)
  have hz : 0 ≤ z := div_nonneg (by linarith) (by linarith)
  have hfrep : x = xa r z := by
    dsimp [xa]
    apply (eq_div_iff (ne_of_gt (show 0 < 1+z by linarith))).2
    have hn0 : 1/(3-2*r)-x ≠ 0 := ne_of_gt (sub_pos.mpr hupper)
    have hzEq : z * (1/(3-2*r)-x) = x-r^2 := div_mul_cancel₀ _ hn0
    simp only [div_eq_mul_inv, one_mul] at hzEq ⊢
    nlinarith only [hzEq]
  exact ⟨r, z, hrlo, hr1, hz, hfrep, hyr⟩

lemma physical_signs (x y : ℝ) (hx : 0 ≤ x) (hx1 : x < 1)
    (hdisc : y^2 ≤ x^3) (hD : 0 < 1-3*x+2*y) :
    0 ≤ A x y ∧ 0 ≤ A x y + C x y ∧ 0 ≤ Lscaled x y := by
  have hyx : y ≤ x := by
    have hpow : x^3 ≤ x^2 := by nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1-x)]
    nlinarith [sq_nonneg (y-x)]
  have hlast : 0 ≤ x^2+x-2*y := by
    by_contra hn
    have hn' : x^2+x < 2*y := by linarith
    have hy : 0 < y := by nlinarith [sq_nonneg x]
    have hp : (x^2+x)^2 < (2*y)^2 := by
      nlinarith [mul_pos (by linarith : 0 < 2*y-(x^2+x))
        (by nlinarith [sq_nonneg x] : 0 < 2*y+(x^2+x))]
    nlinarith [sq_nonneg (x^2-x)]
  have hN1 : 0 ≤ A x y + C x y := by
    rw [N1_factor]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hlast
  rcases eq_or_lt_of_le hx with hzero | hpos
  · have hxzero : x = 0 := hzero.symm
    have hyzero : y = 0 := by rw [hxzero] at hdisc; nlinarith [sq_nonneg y]
    subst x; subst y
    norm_num [A, C, Lscaled]
  · obtain ⟨r, z, hl, hu, hz, hxr, hyr⟩ := physical_parameterization x y hpos hx1 hdisc hD
    have hA : 0 ≤ A x y := by rw [hyr, hxr]; exact A_nonneg_param r z hl hu hz
    have hL : 0 ≤ Lscaled x y := by rw [hyr, hxr]; exact L_nonneg_param r z hl hu hz
    exact ⟨hA, hN1, hL⟩

end ThreeState.Radial

 

namespace ThreeState.Radial

noncomputable def avg (v : Fin 3 → ℝ) : ℝ := (∑ i, v i) / 3
noncomputable def momentX (v : Fin 3 → ℝ) : ℝ := avg (fun i => (v i)^2) / 2
noncomputable def momentY (v : Fin 3 → ℝ) : ℝ := avg (fun i => (v i)^3) / 2
noncomputable def denom (v : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  1 - 3*t^2*momentX v + 2*t^3*momentY v
noncomputable def cofactor (v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  1-v i+(v i)^2-3*momentX v
noncomputable def kernel (v : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) : ℝ :=
  v i-t*((v i)^2-2*momentX v)
noncomputable def centeredLog (v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  Real.log (1+v i) - avg (fun j => Real.log (1+v j))

lemma avg_expand (v : Fin 3 → ℝ) : avg v = (v 0+v 1+v 2)/3 := by
  simp [avg, Fin.sum_univ_succ]; ring

lemma zero_sum_elim (v : Fin 3 → ℝ) (hv : avg v = 0) : v 2 = -v 0-v 1 := by
  rw [avg_expand] at hv; linarith

lemma cubic_identity (v : Fin 3 → ℝ) (hv : avg v = 0) (i : Fin 3) :
    (v i)^3 = 3*momentX v*v i+2*momentY v := by
  have h2 := zero_sum_elim v hv
  fin_cases i
  · change (v 0)^3 = 3*momentX v*v 0+2*momentY v
    simp only [momentX, momentY, avg_expand, h2]; ring
  · change (v 1)^3 = 3*momentX v*v 1+2*momentY v
    simp only [momentX, momentY, avg_expand, h2]; ring
  · change (v 2)^3 = 3*momentX v*v 2+2*momentY v
    simp only [momentX, momentY, avg_expand, h2]; ring

lemma denom_product (v : Fin 3 → ℝ) (hv : avg v = 0) (t : ℝ) :
    denom v t = (1+t*v 0)*(1+t*v 1)*(1+t*v 2) := by
  have h2 := zero_sum_elim v hv
  simp only [denom, momentX, momentY, avg_expand, h2]
  ring

lemma cofactor_identity (v : Fin 3 → ℝ) (hv : avg v = 0) (i : Fin 3) :
    (1+v i) * cofactor v i = denom v 1 := by
  dsimp [cofactor, denom]
  nlinarith only [cubic_identity v hv i]

lemma message_segment_pos (v : Fin 3 → ℝ) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 3) : 0 < 1+t*v i := by
  have hv := hp i
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; norm_num
  · have : 0 < t*(1+v i) := mul_pos h hv
    nlinarith

lemma denom_pos (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < denom v t := by
  rw [denom_product v hv t]
  exact mul_pos (mul_pos (message_segment_pos v hp t ht0 ht1 0)
    (message_segment_pos v hp t ht0 ht1 1)) (message_segment_pos v hp t ht0 ht1 2)

lemma momentX_nonneg (v : Fin 3 → ℝ) : 0 ≤ momentX v := by
  simp only [momentX, avg_expand]; positivity

lemma discriminant (v : Fin 3 → ℝ) (hv : avg v = 0) :
    (v 0-v 1)^2*(v 0-v 2)^2*(v 1-v 2)^2 =
      108*((momentX v)^3-(momentY v)^2) := by
  have h2 := zero_sum_elim v hv
  simp only [momentX, momentY, avg_expand, h2]
  ring

lemma discriminant_nonneg (v : Fin 3 → ℝ) (hv : avg v = 0) :
    (momentY v)^2 ≤ (momentX v)^3 := by
  have h := discriminant v hv
  have : 0 ≤ (v 0-v 1)^2*(v 0-v 2)^2*(v 1-v 2)^2 := by positivity
  linarith

lemma momentX_lt_one (v : Fin 3 → ℝ) (hv : avg v = 0)
    (hp : ∀ i, 0 < 1+v i) : momentX v < 1 := by
  have hu := zero_sum_elim v hv
  have h01 := mul_pos (hp 0) (hp 1)
  have h02 := mul_pos (hp 0) (hp 2)
  have h12 := mul_pos (hp 1) (hp 2)
  simp only [momentX, avg_expand]
  rw [hu] at *
  nlinarith

lemma momentY_le_X (v : Fin 3 → ℝ) (hv : avg v = 0)
    (hp : ∀ i, 0 < 1+v i) : momentY v ≤ momentX v := by
  have hX := momentX_nonneg v
  have hX1 := momentX_lt_one v hv hp
  have hdisc := discriminant_nonneg v hv
  have hpow : (momentX v)^3 ≤ (momentX v)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (momentX v)) (by linarith : 0 ≤ 1-momentX v)]
  nlinarith [sq_nonneg (momentY v-momentX v)]

lemma denom_le_one (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : denom v t ≤ 1 := by
  have h1 := mul_le_mul_of_nonneg_left (momentY_le_X v hv hp) (pow_nonneg ht0 3)
  have h2 := mul_nonneg (mul_nonneg (sq_nonneg t) (momentX_nonneg v))
    (show 0 ≤ 1-t by linarith)
  have h3 : 0 ≤ t^2*momentX v := mul_nonneg (sq_nonneg t) (momentX_nonneg v)
  dsimp [denom]
  nlinarith

noncomputable def cofMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => (cofactor v i)^j)

lemma cofMoment_one (v : Fin 3 → ℝ) (hv : avg v = 0) :
    cofMoment v 1 = 1-momentX v := by
  have h2 := zero_sum_elim v hv
  simp only [cofMoment, cofactor, momentX, avg_expand, h2]
  ring

lemma cofMoment_two (v : Fin 3 → ℝ) (hv : avg v = 0) :
    cofMoment v 2 = 3*(momentX v)^2-4*momentY v+1 := by
  have h2 := zero_sum_elim v hv
  simp only [cofMoment, cofactor, momentX, momentY, avg_expand, h2]
  ring

lemma cofMoment_three (v : Fin 3 → ℝ) (hv : avg v = 0) :
    cofMoment v 3 = -9*(momentX v)^3+9*(momentX v)^2+
      6*momentX v*momentY v+3*momentX v+4*(momentY v)^2-14*momentY v+1 := by
  have h2 := zero_sum_elim v hv
  simp only [cofMoment, cofactor, momentX, momentY, avg_expand, h2]
  ring

noncomputable def numerator (v : Fin 3 → ℝ) (t : ℝ) :=
  (4/5 : ℝ) * avg (fun i => kernel v t i *
    ((cofactor v i)^2*denom v 1-3*cofactor v i*(denom v 1)^2+
      (2*cofMoment v 3-3*cofMoment v 2*denom v 1)*v i))

lemma numerator_expansion (v : Fin 3 → ℝ) (hv : avg v = 0) (t : ℝ) :
    numerator v t = (24/5 : ℝ)*(A (momentX v) (momentY v)+t*C (momentX v) (momentY v)) := by
  unfold numerator
  rw [cofMoment_two v hv, cofMoment_three v hv]
  have h2 := zero_sum_elim v hv
  simp only [cofactor, kernel, denom, A, C, momentX, momentY, avg_expand, h2]
  ring

lemma integral_avg (f : Fin 3 → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (f i) MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, avg (fun i => f i t)) = avg (fun i => ∫ t in (0 : ℝ)..1, f i t) := by
  unfold avg
  rw [intervalIntegral.integral_div, intervalIntegral.integral_finsetSum (fun i _ => hf i)]

lemma log_integral (a : ℝ) (ha : 0 < 1+a) :
    Real.log (1+a) = ∫ t in (0 : ℝ)..1, a/(1+t*a) := by
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < 1+t*a := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hz | hz
    · rw [← hz]; norm_num
    · nlinarith [mul_pos hz ha, ht.2]
  have hc : ContinuousOn (fun t : ℝ => a/(1+t*a)) (Set.Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => ne_of_gt (hp t ht))
  have hi : IntervalIntegrable (fun t : ℝ => a/(1+t*a)) MeasureTheory.volume 0 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num)
  have hD : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.log (1+t*a)) (a/(1+t*a)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
    simpa using (((hasDerivAt_id t).mul_const a).const_add 1).log (ne_of_gt (hp t ht'))
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt hD hi).symm

lemma kernel_div_identity (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 3) :
    v i/(1+t*v i)-avg (fun j => v j/(1+t*v j)) = kernel v t i/denom v t := by
  have h0 := ne_of_gt (message_segment_pos v hp t ht0 ht1 0)
  have h1 := ne_of_gt (message_segment_pos v hp t ht0 ht1 1)
  have h2 := ne_of_gt (message_segment_pos v hp t ht0 ht1 2)
  have h0c : 1+v 0*t ≠ 0 := by simpa [mul_comm] using h0
  have h1c : 1+v 1*t ≠ 0 := by simpa [mul_comm] using h1
  have h2c : 1+v 2*t ≠ 0 := by simpa [mul_comm] using h2
  have hv2 := zero_sum_elim v hv
  rw [denom_product v hv t]
  fin_cases i
  · change v 0/(1+t*v 0)-avg (fun j => v j/(1+t*v j)) =
      kernel v t 0/((1+t*v 0)*(1+t*v 1)*(1+t*v 2))
    simp only [avg_expand, kernel, momentX]
    field_simp [h0, h1, h2, h0c, h1c, h2c]
    rw [hv2]
    ring
  · change v 1/(1+t*v 1)-avg (fun j => v j/(1+t*v j)) =
      kernel v t 1/((1+t*v 0)*(1+t*v 1)*(1+t*v 2))
    simp only [avg_expand, kernel, momentX]
    field_simp [h0, h1, h2, h0c, h1c, h2c]
    rw [hv2]
    ring
  · change v 2/(1+t*v 2)-avg (fun j => v j/(1+t*v j)) =
      kernel v t 2/((1+t*v 0)*(1+t*v 1)*(1+t*v 2))
    simp only [avg_expand, kernel, momentX]
    field_simp [h0, h1, h2, h0c, h1c, h2c]
    rw [hv2]
    ring

lemma centeredLog_integral (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (i : Fin 3) : centeredLog v i = ∫ t in (0 : ℝ)..1, kernel v t i / denom v t := by
  have hi : ∀ j, IntervalIntegrable (fun t : ℝ => v j/(1+t*v j)) MeasureTheory.volume 0 1 := by
    intro j
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    refine continuousOn_const.div (by fun_prop) ?_
    intro t ht
    exact ne_of_gt (message_segment_pos v hp t ht.1 ht.2 j)
  have ha : IntervalIntegrable (fun t : ℝ => avg (fun j => v j/(1+t*v j)))
      MeasureTheory.volume 0 1 := by
    unfold avg
    exact (IntervalIntegrable.sum Finset.univ (fun j _ => hi j)).div_const 3
  unfold centeredLog
  rw [log_integral (v i) (hp i)]
  have hlogs : (fun j => Real.log (1+v j)) = (fun j => ∫ t in (0 : ℝ)..1, v j/(1+t*v j)) := by
    funext j; exact log_integral (v j) (hp j)
  rw [hlogs, ← integral_avg _ hi, ← intervalIntegral.integral_sub (hi i) ha]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
  exact kernel_div_identity v hv hp t ht'.1 ht'.2 i

noncomputable def invMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => ((1+v i)⁻¹)^j)
noncomputable def logInvMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => centeredLog v i*((1+v i)⁻¹)^j)
noncomputable def logMoment (v : Fin 3 → ℝ) := avg (fun i => v i*centeredLog v i)

 
noncomputable def gExpr (v : Fin 3 → ℝ) :=
  6-12*invMoment v 1+8*invMoment v 2-2*invMoment v 3+
  (4/5 : ℝ)*(logInvMoment v 2-3*logInvMoment v 1+
    (2*invMoment v 3-3*invMoment v 2)*logMoment v+
    3*(invMoment v 1-1)*(invMoment v 2-invMoment v 1))
noncomputable def rCore (v : Fin 3 → ℝ) :=
  (6-12*(momentX v)^2)*(denom v 1)^3-12*cofMoment v 1*(denom v 1)^2+
  8*cofMoment v 2*denom v 1-2*cofMoment v 3+
  (12/5 : ℝ)*(cofMoment v 1-denom v 1)*(cofMoment v 2-cofMoment v 1*denom v 1)
noncomputable def logCoeff (v : Fin 3 → ℝ) (i : Fin 3) :=
  (cofactor v i)^2*denom v 1-3*cofactor v i*(denom v 1)^2+
    (2*cofMoment v 3-3*cofMoment v 2*denom v 1)*v i

lemma inv_cofactor (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (i : Fin 3) : (1+v i)⁻¹ = cofactor v i / denom v 1 := by
  apply (eq_div_iff (ne_of_gt (denom_pos v hv hp 1 (by norm_num) le_rfl))).2
  rw [← cofactor_identity v hv i]
  field_simp [ne_of_gt (hp i)]

lemma RN_algebra (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i) :
    (denom v 1)^3*(gExpr v-12*(momentX v)^2) =
      rCore v + (4/5 : ℝ)*avg (fun i => centeredLog v i*logCoeff v i) := by
  have hD := ne_of_gt (denom_pos v hv hp 1 (by norm_num) le_rfl)
  unfold gExpr invMoment logInvMoment logMoment rCore logCoeff
  simp_rw [inv_cofactor v hv hp]
  simp only [cofMoment, avg_expand]
  field_simp
  ring

lemma kernel_div_integrable (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (i : Fin 3) : IntervalIntegrable (fun t : ℝ => kernel v t i/denom v t)
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  unfold kernel denom
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro t ht
  exact ne_of_gt (denom_pos v hv hp t ht.1 ht.2)

lemma RN_representation (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i) :
    (denom v 1)^3*(gExpr v-12*(momentX v)^2) =
      rCore v + ∫ t in (0 : ℝ)..1, numerator v t / denom v t := by
  rw [RN_algebra v hv hp]
  congr 1
  have hg : ∀ t : ℝ, numerator v t/denom v t = (4/5 : ℝ)*
      avg (fun i => (kernel v t i/denom v t)*logCoeff v i) := by
    intro t
    simp only [numerator, logCoeff, avg_expand]
    ring
  simp_rw [hg]
  rw [intervalIntegral.integral_const_mul, integral_avg _
    (fun i => (kernel_div_integrable v hv hp i).mul_const (logCoeff v i))]
  congr 1
  congr 1
  funext i
  rw [intervalIntegral.integral_mul_const, centeredLog_integral v hv hp i]

lemma integrate_N_lower (a c x y : ℝ) :
    (∫ t in (0 : ℝ)..1, (24/5 : ℝ)*(a+t*c)*(1+3*t^2*x-2*t^3*y)) =
      (24/5 : ℝ)*(a+c/2+a*x+(3*c*x-2*a*y)/4-2*c*y/5) := by
  let P := fun t : ℝ => (24/5 : ℝ)*(a*t+c*t^2/2+a*x*t^3+
      (3*c*x-2*a*y)*t^4/4-2*c*y*t^5/5)
  have hd : ∀ t : ℝ, HasDerivAt P ((24/5 : ℝ)*(a+t*c)*(1+3*t^2*x-2*t^3*y)) t := by
    intro t
    dsimp [P]
    convert (((((hasDerivAt_id t).const_mul a).add
      (((hasDerivAt_id t).pow 2).const_mul c |>.div_const 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (a*x))).add
      (((hasDerivAt_id t).pow 4).const_mul (3*c*x-2*a*y) |>.div_const 4) |>.sub
      (((hasDerivAt_id t).pow 5).const_mul (2*c*y) |>.div_const 5)).const_mul (24/5 : ℝ) using 1 <;>
      first | rfl | (norm_num; ring)
  have hi : IntervalIntegrable (fun t : ℝ => (24/5 : ℝ)*(a+t*c)*(1+3*t^2*x-2*t^3*y))
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by fun_prop) 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
  dsimp [P]; ring

lemma L_expansion (v : Fin 3 → ℝ) (hv : avg v = 0) :
    rCore v + (∫ t in (0 : ℝ)..1, numerator v t*(2-denom v t)) =
      (6/25 : ℝ)*Lscaled (momentX v) (momentY v) := by
  have hg : (fun t : ℝ => numerator v t*(2-denom v t)) =
    (fun t : ℝ => (24/5 : ℝ)*(A (momentX v) (momentY v)+t*C (momentX v) (momentY v))*
      (1+3*t^2*momentX v-2*t^3*momentY v)) := by
    funext t
    rw [numerator_expansion v hv t]
    dsimp [denom]; ring
  rw [hg, integrate_N_lower]
  unfold rCore
  rw [cofMoment_one v hv, cofMoment_two v hv, cofMoment_three v hv]
  dsimp [denom, A, C, Lscaled]
  ring

lemma numerator_nonneg (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ numerator v t := by
  have hD : 0 < 1-3*momentX v+2*momentY v := by
    simpa [denom] using denom_pos v hv hp 1 (by norm_num) le_rfl
  obtain ⟨ha, hac, _⟩ := physical_signs (momentX v) (momentY v)
    (momentX_nonneg v) (momentX_lt_one v hv hp) (discriminant_nonneg v hv) hD
  rw [numerator_expansion v hv t]
  have h := add_nonneg (mul_nonneg (show 0 ≤ 1-t by linarith) ha) (mul_nonneg ht0 hac)
  nlinarith only [h]

 

lemma gExpr_lower (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i) :
    12*(momentX v)^2 ≤ gExpr v := by
  have hi1 : IntervalIntegrable (fun t => numerator v t*(2-denom v t))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold numerator kernel denom avg
    fun_prop
  have hi2 : IntervalIntegrable (fun t => numerator v t/denom v t)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.div
    · unfold numerator kernel avg; fun_prop
    · unfold denom; fun_prop
    · intro t ht; exact ne_of_gt (denom_pos v hv hp t ht.1 ht.2)
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, numerator v t*(2-denom v t) ≤ numerator v t/denom v t := by
    intro t ht
    have hD := denom_pos v hv hp t ht.1 ht.2
    apply (le_div_iff₀ hD).2
    nlinarith [mul_nonneg (numerator_nonneg v hv hp t ht.1 ht.2) (sq_nonneg (1-denom v t))]
  have hint := intervalIntegral.integral_mono_on (by norm_num) hi1 hi2 hbound
  have hR := RN_representation v hv hp
  have hL := L_expansion v hv
  have hd := denom_pos v hv hp 1 (by norm_num) le_rfl
  have hdom : 0 < 1-3*momentX v+2*momentY v := by simpa [denom] using hd
  have hLpos := (physical_signs (momentX v) (momentY v) (momentX_nonneg v)
    (momentX_lt_one v hv hp) (discriminant_nonneg v hv) hdom).2.2
  have hprod : 0 ≤ (denom v 1)^3*(gExpr v-12*(momentX v)^2) := by linarith
  have := nonneg_of_mul_nonneg_right hprod (pow_pos hd 3)
  linarith

end ThreeState.Radial

end OAI
