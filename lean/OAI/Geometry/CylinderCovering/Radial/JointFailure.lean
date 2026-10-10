import OAI.Geometry.CylinderCovering.Radial.CapCoverage

namespace OAI

noncomputable section
namespace CylinderCovering.RadialCapCoverage

private theorem joint_product_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B)
    (hA : 0 ≤ A) : |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) hA

theorem joint_failure_estimate {eps x y t p q : ℝ}
    (heps : 0 < eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hfq : 1 < 1 - t + eps * x * q)
    (hfp : 1 < 1 + t - eps * y * p) :
    |t| ≤ 2 * eps ∧ |x - p| ≤ 3 * eps ∧ |y - q| ≤ 3 * eps ∧
      |t - eps * p * q| ≤ 3 * eps ^ 2 ∧
      eps * (x * q - y * p) ≤
        eps ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * eps ^ 3 := by
  have hep : 0 ≤ eps := heps.le
  have hp2 : p ^ 2 ≤ 1 := by nlinarith only [hp, sq_abs p, abs_nonneg p]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [hq, sq_abs q, abs_nonneg q]
  let dp := (1 - p ^ 2) / 2
  let dq := (1 - q ^ 2) / 2
  have hdp : 0 ≤ dp ∧ dp ≤ 1 / 2 := by dsimp [dp]; constructor <;> nlinarith only [hp2, sq_nonneg p]
  have hdq : 0 ≤ dq ∧ dq ≤ 1 / 2 := by dsimp [dq]; constructor <;> nlinarith only [hq2, sq_nonneg q]
  have htl : eps * y * p < t := by linarith only [hfp]
  have htu : t < eps * x * q := by linarith only [hfq]
  have hxp0 : |x * q| ≤ 2 := by simpa using joint_product_bound hx hq (by norm_num)
  have hyp0 : |y * p| ≤ 2 := by simpa using joint_product_bound hy hp (by norm_num)
  have ht : |t| ≤ 2 * eps := by
    have h1 := (abs_le.mp hyp0).1
    have h2 := (abs_le.mp hxp0).2
    rw [abs_le]
    constructor <;> nlinarith only [htl, htu, mul_le_mul_of_nonneg_left h1 hep,
      mul_le_mul_of_nonneg_left h2 hep]
  have hxp : |x - p| ≤ 3 * eps := by
    have ht1 : |t * p| ≤ 2 * eps := by simpa using joint_product_bound ht hp (by positivity)
    have hy1 : |y * dp| ≤ 1 := by
      have hh := joint_product_bound hy (show |dp| ≤ 1 / 2 by rw [abs_of_nonneg hdp.1]; exact hdp.2) (by norm_num)
      norm_num at hh ⊢
      exact hh
    have hy2 : |eps * (y * dp)| ≤ eps := by
      simpa using joint_product_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hy1 hep
    have heq : x - p = t * p + eps * (y * dp) := by dsimp [dp]; nlinarith only [hrootp]
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith only [ht1, hy2])
  have hyq : |y - q| ≤ 3 * eps := by
    have ht1 : |t * q| ≤ 2 * eps := by simpa using joint_product_bound ht hq (by positivity)
    have hx1 : |x * dq| ≤ 1 := by
      have hh := joint_product_bound hx (show |dq| ≤ 1 / 2 by rw [abs_of_nonneg hdq.1]; exact hdq.2) (by norm_num)
      norm_num at hh ⊢
      exact hh
    have hx2 : |eps * (x * dq)| ≤ eps := by
      simpa using joint_product_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hx1 hep
    have heq : y - q = -(t * q + eps * (x * dq)) := by dsimp [dq]; nlinarith only [hrootq]
    rw [heq, abs_neg]
    exact (abs_add_le _ _).trans (by linarith only [ht1, hx2])
  have hpq : |p * q| ≤ 1 := by simpa using joint_product_bound hp hq (by norm_num)
  have hxe : |eps * q * (x - p)| ≤ 3 * eps ^ 2 := by
    have h1 : |eps * q| ≤ eps := by
      simpa using joint_product_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hq hep
    convert joint_product_bound h1 hxp hep using 1
    ring
  have hye : |eps * p * (y - q)| ≤ 3 * eps ^ 2 := by
    have h1 : |eps * p| ≤ eps := by
      simpa using joint_product_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hp hep
    convert joint_product_bound h1 hyq hep using 1
    ring
  have htinterface : |t - eps * p * q| ≤ 3 * eps ^ 2 := by
    rw [abs_le]
    constructor
    · have hh := (abs_le.mp hye).1
      nlinarith only [hh, htl]
    · have hh := (abs_le.mp hxe).2
      nlinarith only [hh, htu]
  have htcoeff : |2 * eps * (p * q)| ≤ 2 * eps := by
    simpa using joint_product_bound (show |2 * eps| ≤ 2 * eps by rw [abs_of_nonneg (by positivity)]) hpq (by positivity)
  have hterr : |2 * eps * (p * q) * (t - eps * p * q)| ≤ 6 * eps ^ 3 := by
    convert joint_product_bound htcoeff htinterface (by positivity) using 1
    ring
  have hqD : |q * dp| ≤ 1 / 2 := by
    simpa using joint_product_bound hq (show |dp| ≤ 1 / 2 by rw [abs_of_nonneg hdp.1]; exact hdp.2) (by norm_num)
  have hpD : |p * dq| ≤ 1 / 2 := by
    simpa using joint_product_bound hp (show |dq| ≤ 1 / 2 by rw [abs_of_nonneg hdq.1]; exact hdq.2) (by norm_num)
  have herrq : |(y - q) * (q * dp)| ≤ 3 * eps / 2 := by
    convert joint_product_bound hyq hqD (by positivity) using 1
    ring
  have herrp : |(x - p) * (p * dq)| ≤ 3 * eps / 2 := by
    convert joint_product_bound hxp hpD (by positivity) using 1
    ring
  have heq : eps * (x * q - y * p) = 2 * eps * p * q * t +
      eps ^ 2 * (y * q * dp + x * p * dq) := by
    dsimp [dp, dq]
    linear_combination eps * q * hrootp - eps * p * hrootq
  have hmain : eps * (x * q - y * p) ≤
      eps ^ 2 * ((p ^ 2 + q ^ 2) / 2 + p ^ 2 * q ^ 2) + 9 * eps ^ 3 := by
    have hte := (abs_le.mp hterr).2
    have hqe := mul_le_mul_of_nonneg_left (abs_le.mp herrq).2 (sq_nonneg eps)
    have hpe := mul_le_mul_of_nonneg_left (abs_le.mp herrp).2 (sq_nonneg eps)
    dsimp [dp, dq] at heq hqe hpe
    nlinarith only [heq, hte, hqe, hpe]
  have hpoly : (p ^ 2 + q ^ 2) / 2 + p ^ 2 * q ^ 2 ≤
      RadialCaps.H p + RadialCaps.H q := by
    unfold RadialCaps.H
    nlinarith only [sq_nonneg (p ^ 2 - q ^ 2)]
  have hfinal : eps * (x * q - y * p) ≤
      eps ^ 2 * (RadialCaps.H p + RadialCaps.H q) + 9 * eps ^ 3 := hmain.trans (by
    have hh := mul_le_mul_of_nonneg_left hpoly (sq_nonneg eps)
    linarith only [hh])
  exact ⟨ht, hxp, hyq, htinterface, hfinal⟩

end CylinderCovering.RadialCapCoverage

end

end OAI
