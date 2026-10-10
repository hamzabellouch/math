import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.RadialOverlapBounds

private theorem abs_mul_le {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B)
    (hA : 0 ≤ A) : |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) hA

theorem root_estimates {eps x y t p q : ℝ}
    (heps : 0 ≤ eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hlower : eps * y * p ≤ t) (hupper : t ≤ eps * x * q) :
    |t| ≤ 2 * eps ∧ |x - p| ≤ 3 * eps ∧ |y - q| ≤ 3 * eps := by
  have hxp : |x * q| ≤ 2 := by
    simpa using abs_mul_le hx hq (by norm_num)
  have hyp : |y * p| ≤ 2 := by
    simpa using abs_mul_le hy hp (by norm_num)
  have ht : |t| ≤ 2 * eps := by
    rw [abs_le]
    constructor
    · have h := mul_le_mul_of_nonneg_left (abs_le.mp hyp).1 heps
      nlinarith only [h, hlower]
    · have h := mul_le_mul_of_nonneg_left (abs_le.mp hxp).2 heps
      nlinarith only [h, hupper]
  have hp2 : p ^ 2 ≤ 1 := by
    nlinarith only [hp, sq_abs p, abs_nonneg p]
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith only [hq, sq_abs q, abs_nonneg q]
  have hdp : |(1 - p ^ 2) / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hp2, sq_nonneg p]
  have hdq : |(1 - q ^ 2) / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hq2, sq_nonneg q]
  have htp : |t * p| ≤ 2 * eps := by
    simpa using abs_mul_le ht hp (by positivity)
  have htq : |t * q| ≤ 2 * eps := by
    simpa using abs_mul_le ht hq (by positivity)
  have heyp : |eps * (y * ((1 - p ^ 2) / 2))| ≤ eps := by
    have hyD : |y * ((1 - p ^ 2) / 2)| ≤ 1 := by
      simpa using abs_mul_le hy hdp (by norm_num)
    simpa using abs_mul_le (show |eps| ≤ eps by rw [abs_of_nonneg heps]) hyD heps
  have hexq : |eps * (x * ((1 - q ^ 2) / 2))| ≤ eps := by
    have hxD : |x * ((1 - q ^ 2) / 2)| ≤ 1 := by
      simpa using abs_mul_le hx hdq (by norm_num)
    simpa using abs_mul_le (show |eps| ≤ eps by rw [abs_of_nonneg heps]) hxD heps
  refine ⟨ht, ?_, ?_⟩
  · have hid : x - p = t * p + eps * (y * ((1 - p ^ 2) / 2)) := by
      nlinarith only [hrootp]
    rw [hid]
    exact (abs_add_le _ _).trans (by linarith only [htp, heyp])
  · have hid : y - q = -(t * q + eps * (x * ((1 - q ^ 2) / 2))) := by
      nlinarith only [hrootq]
    rw [hid, abs_neg]
    exact (abs_add_le _ _).trans (by linarith only [htq, hexq])

theorem excess_identity (eps x y t p q : ℝ) :
    (1 - t + eps * x * q) + (1 + t - eps * y * p) - 2 =
      eps * ((x - p) * q - (y - q) * p) := by
  ring

theorem joint_radial_bounds {eps x y t p q : ℝ}
    (heps : 0 ≤ eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hrho : 1 ≤ 1 - t + eps * x * q)
    (hsigma : 1 ≤ 1 + t - eps * y * p) :
    let rho := 1 - t + eps * x * q
    let sigma := 1 + t - eps * y * p
    0 ≤ rho + sigma - 2 ∧
    rho + sigma - 2 ≤ 6 * eps ^ 2 ∧
    0 ≤ rho - 1 ∧ rho - 1 ≤ rho + sigma - 2 ∧
    0 ≤ sigma - 1 ∧ sigma - 1 ≤ rho + sigma - 2 ∧
    |rho - sigma| ≤ rho + sigma - 2 := by
  dsimp only
  obtain ⟨ht, hxp, hyq⟩ := root_estimates heps hx hy hp hq hrootq hrootp
    (by linarith only [hsigma]) (by linarith only [hrho])
  have hfirst : |(x - p) * q| ≤ 3 * eps := by
    simpa using abs_mul_le hxp hq (by positivity)
  have hsecond : |(y - q) * p| ≤ 3 * eps := by
    simpa using abs_mul_le hyq hp (by positivity)
  have hdiff : |(x - p) * q - (y - q) * p| ≤ 6 * eps :=
    (abs_sub _ _).trans (by linarith only [hfirst, hsecond])
  have hsum : (1 - t + eps * x * q) + (1 + t - eps * y * p) - 2 ≤
      6 * eps ^ 2 := by
    rw [excess_identity]
    have h := mul_le_mul_of_nonneg_left (abs_le.mp hdiff).2 heps
    nlinarith only [h]
  refine ⟨by linarith only [hrho, hsigma], hsum,
    by linarith only [hrho], by linarith only [hsigma],
    by linarith only [hsigma], by linarith only [hrho], ?_⟩
  rw [abs_le]
  constructor <;> linarith only [hrho, hsigma]

theorem individual_radial_bounds {eps x y t p q : ℝ}
    (heps : 0 ≤ eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hrho : 1 ≤ 1 - t + eps * x * q)
    (hsigma : 1 ≤ 1 + t - eps * y * p) :
    let rho := 1 - t + eps * x * q
    let sigma := 1 + t - eps * y * p
    rho - 1 ≤ 12 * eps ^ 2 ∧ sigma - 1 ≤ 12 * eps ^ 2 ∧
      |rho - sigma| ≤ 12 * eps ^ 2 := by
  dsimp only
  obtain ⟨_, hsum, _, hr, _, hs, hd⟩ :=
    joint_radial_bounds heps hx hy hp hq hrootq hrootp hrho hsigma
  constructor
  · nlinarith only [hsum, hr, sq_nonneg eps]
  constructor
  · nlinarith only [hsum, hs, sq_nonneg eps]
  · nlinarith only [hsum, hd, sq_nonneg eps]

theorem interface_error {eps x y t p q : ℝ}
    (heps : 0 ≤ eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hlower : eps * y * p ≤ t) (hupper : t ≤ eps * x * q) :
    |t - eps * p * q| ≤ 3 * eps ^ 2 := by
  obtain ⟨_, hxp, hyq⟩ := root_estimates heps hx hy hp hq hrootq hrootp hlower hupper
  have hxe : |eps * ((x - p) * q)| ≤ 3 * eps ^ 2 := by
    have h := abs_mul_le hxp hq (by positivity)
    have h' := abs_mul_le (show |eps| ≤ eps by rw [abs_of_nonneg heps]) h heps
    nlinarith only [h']
  have hye : |eps * ((y - q) * p)| ≤ 3 * eps ^ 2 := by
    have h := abs_mul_le hyq hp (by positivity)
    have h' := abs_mul_le (show |eps| ≤ eps by rw [abs_of_nonneg heps]) h heps
    nlinarith only [h']
  rw [abs_le]
  constructor
  · have h := (abs_le.mp hye).1
    nlinarith only [h, hlower]
  · have h := (abs_le.mp hxe).2
    nlinarith only [h, hupper]

theorem cap_comparison {eps x y t p q : ℝ}
    (heps : 0 ≤ eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hlower : eps * y * p ≤ t) (hupper : t ≤ eps * x * q) :
    eps * (x * q - y * p) ≤
      eps ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * eps ^ 3 := by
  obtain ⟨_, hxp, hyq⟩ := root_estimates heps hx hy hp hq hrootq hrootp hlower hupper
  have ht := interface_error heps hx hy hp hq hrootq hrootp hlower hupper
  have hp2 : p ^ 2 ≤ 1 := by
    nlinarith only [hp, sq_abs p, abs_nonneg p]
  have hq2 : q ^ 2 ≤ 1 := by
    nlinarith only [hq, sq_abs q, abs_nonneg q]
  have hdp : |(1 - p ^ 2) / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hp2, sq_nonneg p]
  have hdq : |(1 - q ^ 2) / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [hq2, sq_nonneg q]
  have hpq : |p * q| ≤ 1 := by simpa using abs_mul_le hp hq (by norm_num)
  have hcoeff : |2 * eps * (p * q)| ≤ 2 * eps := by
    simpa using abs_mul_le
      (show |2 * eps| ≤ 2 * eps by rw [abs_of_nonneg (by positivity)]) hpq (by positivity)
  have hterr : |2 * eps * (p * q) * (t - eps * p * q)| ≤ 6 * eps ^ 3 := by
    convert abs_mul_le hcoeff ht (by positivity) using 1
    ring
  have hqD : |q * ((1 - p ^ 2) / 2)| ≤ 1 / 2 := by
    simpa using abs_mul_le hq hdp (by norm_num)
  have hpD : |p * ((1 - q ^ 2) / 2)| ≤ 1 / 2 := by
    simpa using abs_mul_le hp hdq (by norm_num)
  have herrq : |(y - q) * (q * ((1 - p ^ 2) / 2))| ≤ 3 * eps / 2 := by
    convert abs_mul_le hyq hqD (by positivity) using 1
    ring
  have herrp : |(x - p) * (p * ((1 - q ^ 2) / 2))| ≤ 3 * eps / 2 := by
    convert abs_mul_le hxp hpD (by positivity) using 1
    ring
  have hid : eps * (x * q - y * p) = 2 * eps * p * q * t +
      eps ^ 2 * (y * q * ((1 - p ^ 2) / 2) + x * p * ((1 - q ^ 2) / 2)) := by
    linear_combination eps * q * hrootp - eps * p * hrootq
  have hmain : eps * (x * q - y * p) ≤
      eps ^ 2 * ((p ^ 2 + q ^ 2) / 2 + p ^ 2 * q ^ 2) + 9 * eps ^ 3 := by
    have hte := (abs_le.mp hterr).2
    have hqe := mul_le_mul_of_nonneg_left (abs_le.mp herrq).2 (sq_nonneg eps)
    have hpe := mul_le_mul_of_nonneg_left (abs_le.mp herrp).2 (sq_nonneg eps)
    nlinarith only [hid, hte, hqe, hpe]
  have hpoly : (p ^ 2 + q ^ 2) / 2 + p ^ 2 * q ^ 2 ≤
      RadialCaps.H p + RadialCaps.H q := by
    unfold RadialCaps.H
    nlinarith only [sq_nonneg (p ^ 2 - q ^ 2)]
  exact hmain.trans (by
    have h := mul_le_mul_of_nonneg_left hpoly (sq_nonneg eps)
    linarith only [h])

theorem cubic_twelve_compensation {eps x y t p q : ℝ}
    (heps : 0 < eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hlower : eps * y * p ≤ t) (hupper : t ≤ eps * x * q) :
    eps * (x * q - y * p) <
      (RadialCaps.cubicCap 12 eps p - 1) + (RadialCaps.cubicCap 12 eps q - 1) := by
  have h := cap_comparison heps.le hx hy hp hq hrootq hrootp hlower hupper
  unfold RadialCaps.cubicCap
  nlinarith only [h, pow_pos heps 3]

theorem physical_cap_comparison {k tau x y z p q : ℝ}
    (hk : 0 < k) (htau : 0 ≤ tau) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : x = (1 - k * z) * q - (k * tau) * y * (1 - q ^ 2) / 2)
    (hrootp : y = (1 + k * z) * p + (k * tau) * x * (1 - p ^ 2) / 2)
    (hlower : tau * x * p ≤ z) (hupper : z ≤ tau * y * q) :
    tau * (y * q - x * p) ≤
      k * tau ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * k ^ 2 * tau ^ 3 := by
  have hl : (k * tau) * x * p ≤ k * z := by
    nlinarith only [mul_le_mul_of_nonneg_left hlower hk.le]
  have hu : k * z ≤ (k * tau) * y * q := by
    nlinarith only [mul_le_mul_of_nonneg_left hupper hk.le]
  have h := cap_comparison (mul_nonneg hk.le htau) hy hx hp hq hrootq hrootp hl hu
  apply (mul_le_mul_iff_right₀ hk).mp
  calc
    k * (tau * (y * q - x * p)) = (k * tau) * (y * q - x * p) := by ring
    _ ≤ (k * tau) ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * (k * tau) ^ 3 := h
    _ = k * (k * tau ^ 2 * (RadialCaps.H p + RadialCaps.H q) +
        9 * k ^ 2 * tau ^ 3) := by ring

theorem orthonormal_height_compensation {tau x y z p q : ℝ}
    (htau : 0 < tau) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : x = (1 - (1 / Real.sqrt 2) * z) * q -
      ((1 / Real.sqrt 2) * tau) * y * (1 - q ^ 2) / 2)
    (hrootp : y = (1 + (1 / Real.sqrt 2) * z) * p +
      ((1 / Real.sqrt 2) * tau) * x * (1 - p ^ 2) / 2)
    (hlower : tau * x * p ≤ z) (hupper : z ≤ tau * y * q) :
    tau * (y * q - x * p) <
      (tau ^ 2 * (1 / Real.sqrt 2) * RadialCaps.H p + 10 * tau ^ 3) +
      (tau ^ 2 * (1 / Real.sqrt 2) * RadialCaps.H q + 10 * tau ^ 3) := by
  have hk : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have h := physical_cap_comparison hk htau.le hx hy hp hq hrootq hrootp hlower hupper
  have hmargin : 9 * (1 / Real.sqrt 2) ^ 2 < (20 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have he := mul_lt_mul_of_pos_right hmargin (pow_pos htau 3)
  nlinarith only [h, he]

end CylinderCovering.RadialOverlapBounds

end

end OAI
