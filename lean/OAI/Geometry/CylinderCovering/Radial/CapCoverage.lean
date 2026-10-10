import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

open Set

noncomputable section
namespace CylinderCovering.RadialCapCoverage

theorem quadratic_crossing {a b y : ℝ} (hay : |y| ≤ a) :
    ∃ q : ℝ, |q| ≤ 1 ∧ y = a * q - b * (1 - q ^ 2) / 2 ∧ 0 ≤ a + b * q := by
  have ha : 0 ≤ a := (abs_nonneg y).trans hay
  by_cases hb : b = 0
  · subst b
    by_cases hza : a = 0
    · subst a
      have hy : y = 0 := abs_eq_zero.mp (le_antisymm hay (abs_nonneg y))
      subst y
      exact ⟨0, by norm_num, by norm_num, by norm_num⟩
    · refine ⟨y / a, ?_, ?_, ?_⟩
      · rw [abs_div, abs_of_nonneg ha]
        exact (div_le_one (lt_of_le_of_ne ha (Ne.symm hza))).mpr hay
      · simp only [zero_mul]
        field_simp; ring
      · simpa using ha
  · have hab : |b * y| ≤ |b| * a := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hay (abs_nonneg b)
    have hlo := (abs_le.mp hab).1
    have hhi := (abs_le.mp hab).2
    have hb2 : |b| ^ 2 = b ^ 2 := sq_abs b
    have hdisc : 0 ≤ a ^ 2 + b ^ 2 + 2 * b * y := by
      nlinarith [sq_nonneg (a - |b|)]
    let r := Real.sqrt (a ^ 2 + b ^ 2 + 2 * b * y)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = a ^ 2 + b ^ 2 + 2 * b * y := Real.sq_sqrt hdisc
    have hupper : r ≤ a + |b| := by nlinarith [abs_nonneg b]
    have hlower : a - |b| ≤ r := by nlinarith [sq_nonneg (a - |b|)]
    have habs : |r - a| ≤ |b| := abs_le.mpr ⟨by linarith, by linarith⟩
    refine ⟨(r - a) / b, ?_, ?_, ?_⟩
    · rw [abs_div]
      exact (div_le_one (abs_pos.mpr hb)).mpr habs
    · field_simp
      nlinarith [hr2]
    · have heq : a + b * ((r - a) / b) = r := by field_simp; ring
      rw [heq]
      exact hr

private theorem abs_mul_bound {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B)
    (hA : 0 ≤ A) : |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) hA

theorem no_double_failure {eps x y t p q bp bq : ℝ}
    (heps : 0 < eps) (hx : |x| ≤ 2) (hy : |y| ≤ 2)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1)
    (hrootq : y = (1 - t) * q - eps * x * (1 - q ^ 2) / 2)
    (hrootp : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2)
    (hbp : 0 ≤ bp) (hbq : 0 ≤ bq) (hpadding : 9 * eps ≤ bp + bq) :
    1 - t + eps * x * q ≤ 1 + eps ^ 2 * (RadialCaps.H q + bq) ∨
      1 + t - eps * y * p ≤ 1 + eps ^ 2 * (RadialCaps.H p + bp) := by
  by_contra hfail
  push Not at hfail
  obtain ⟨hfq, hfp⟩ := hfail
  have hep : 0 ≤ eps := heps.le
  have hp2 : p ^ 2 ≤ 1 := by nlinarith only [hp, sq_abs p, abs_nonneg p]
  have hq2 : q ^ 2 ≤ 1 := by nlinarith only [hq, sq_abs q, abs_nonneg q]
  let dp := (1 - p ^ 2) / 2
  let dq := (1 - q ^ 2) / 2
  have hdp : 0 ≤ dp ∧ dp ≤ 1 / 2 := by dsimp [dp]; constructor <;> nlinarith only [hp2, sq_nonneg p]
  have hdq : 0 ≤ dq ∧ dq ≤ 1 / 2 := by dsimp [dq]; constructor <;> nlinarith only [hq2, sq_nonneg q]
  have hHp : 0 ≤ RadialCaps.H p := by unfold RadialCaps.H; positivity
  have hHq : 0 ≤ RadialCaps.H q := by unfold RadialCaps.H; positivity
  have htl : eps * y * p < t := by nlinarith only [hfp, mul_nonneg (sq_nonneg eps) (add_nonneg hHp hbp)]
  have htu : t < eps * x * q := by nlinarith only [hfq, mul_nonneg (sq_nonneg eps) (add_nonneg hHq hbq)]
  have hxp0 : |x * q| ≤ 2 := by simpa using abs_mul_bound hx hq (by norm_num)
  have hyp0 : |y * p| ≤ 2 := by simpa using abs_mul_bound hy hp (by norm_num)
  have ht : |t| ≤ 2 * eps := by
    have h1 := (abs_le.mp hyp0).1
    have h2 := (abs_le.mp hxp0).2
    rw [abs_le]
    constructor <;> nlinarith only [htl, htu, mul_le_mul_of_nonneg_left h1 hep,
      mul_le_mul_of_nonneg_left h2 hep]
  have hxp : |x - p| ≤ 3 * eps := by
    have ht1 : |t * p| ≤ 2 * eps := by simpa using abs_mul_bound ht hp (by positivity)
    have hy1 : |y * dp| ≤ 1 := by
      have hh := abs_mul_bound hy (show |dp| ≤ 1 / 2 by rw [abs_of_nonneg hdp.1]; exact hdp.2) (by norm_num)
      norm_num at hh ⊢
      exact hh
    have hy2 : |eps * (y * dp)| ≤ eps := by
      simpa using abs_mul_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hy1 hep
    have heq : x - p = t * p + eps * (y * dp) := by dsimp [dp]; nlinarith only [hrootp]
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith only [ht1, hy2])
  have hyq : |y - q| ≤ 3 * eps := by
    have ht1 : |t * q| ≤ 2 * eps := by simpa using abs_mul_bound ht hq (by positivity)
    have hx1 : |x * dq| ≤ 1 := by
      have hh := abs_mul_bound hx (show |dq| ≤ 1 / 2 by rw [abs_of_nonneg hdq.1]; exact hdq.2) (by norm_num)
      norm_num at hh ⊢
      exact hh
    have hx2 : |eps * (x * dq)| ≤ eps := by
      simpa using abs_mul_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hx1 hep
    have heq : y - q = -(t * q + eps * (x * dq)) := by dsimp [dq]; nlinarith only [hrootq]
    rw [heq, abs_neg]
    exact (abs_add_le _ _).trans (by linarith only [ht1, hx2])
  have hpq : |p * q| ≤ 1 := by simpa using abs_mul_bound hp hq (by norm_num)
  have hxe : |eps * q * (x - p)| ≤ 3 * eps ^ 2 := by
    have h1 : |eps * q| ≤ eps := by
      simpa using abs_mul_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hq hep
    convert abs_mul_bound h1 hxp hep using 1
    ring
  have hye : |eps * p * (y - q)| ≤ 3 * eps ^ 2 := by
    have h1 : |eps * p| ≤ eps := by
      simpa using abs_mul_bound (show |eps| ≤ eps by rw [abs_of_nonneg hep]) hp hep
    convert abs_mul_bound h1 hyq hep using 1
    ring
  have htinterface : |t - eps * p * q| ≤ 3 * eps ^ 2 := by
    rw [abs_le]
    constructor
    · have hh := (abs_le.mp hye).1
      nlinarith only [hh, htl]
    · have hh := (abs_le.mp hxe).2
      nlinarith only [hh, htu]
  have htcoeff : |2 * eps * (p * q)| ≤ 2 * eps := by
    simpa using abs_mul_bound (show |2 * eps| ≤ 2 * eps by rw [abs_of_nonneg (by positivity)]) hpq (by positivity)
  have hterr : |2 * eps * (p * q) * (t - eps * p * q)| ≤ 6 * eps ^ 3 := by
    convert abs_mul_bound htcoeff htinterface (by positivity) using 1
    ring
  have hqD : |q * dp| ≤ 1 / 2 := by
    simpa using abs_mul_bound hq (show |dp| ≤ 1 / 2 by rw [abs_of_nonneg hdp.1]; exact hdp.2) (by norm_num)
  have hpD : |p * dq| ≤ 1 / 2 := by
    simpa using abs_mul_bound hp (show |dq| ≤ 1 / 2 by rw [abs_of_nonneg hdq.1]; exact hdq.2) (by norm_num)
  have herrq : |(y - q) * (q * dp)| ≤ 3 * eps / 2 := by
    convert abs_mul_bound hyq hqD (by positivity) using 1
    ring
  have herrp : |(x - p) * (p * dq)| ≤ 3 * eps / 2 := by
    convert abs_mul_bound hxp hpD (by positivity) using 1
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
  have hpad := mul_le_mul_of_nonneg_left hpadding (sq_nonneg eps)
  nlinarith only [hfq, hfp, hfinal, hpad]

theorem padding_coverage {eps : ℝ} {R b : ℝ → ℝ}
    (heps : 0 < eps)
    (hcap : ∀ r ∈ Icc (-1 : ℝ) 1, R r = 1 + eps ^ 2 * (RadialCaps.H r + b r))
    (hb : ∀ r ∈ Icc (-1 : ℝ) 1, 0 ≤ b r)
    (hpadding : ∀ p ∈ Icc (-1 : ℝ) 1, ∀ q ∈ Icc (-1 : ℝ) 1,
      9 * eps ≤ b p + b q)
    {x y t : ℝ} (hx : |x| ≤ 1 + t) (hy : |y| ≤ 1 - t) :
    (∃ q rho : ℝ, |q| ≤ 1 ∧ 0 ≤ rho ∧ rho ≤ R q ∧
      y = rho * q - eps * x * RadialCaps.G q ∧ t = 1 - rho + eps * x * q) ∨
    (∃ p sigma : ℝ, |p| ≤ 1 ∧ 0 ≤ sigma ∧ sigma ≤ R p ∧
      x = sigma * p + eps * y * RadialCaps.G p ∧ t = -1 + sigma + eps * y * p) := by
  obtain ⟨q, hq, hrootq, hrho⟩ := quadratic_crossing (b := eps * x) hy
  obtain ⟨p, hp, hrootp, hsigma⟩ := quadratic_crossing (b := -(eps * y)) hx
  have hrootp' : x = (1 + t) * p + eps * y * (1 - p ^ 2) / 2 := by
    nlinarith only [hrootp]
  have hx2 : |x| ≤ 2 := by linarith only [hx, hy, abs_nonneg y]
  have hy2 : |y| ≤ 2 := by linarith only [hx, hy, abs_nonneg x]
  have hpI : p ∈ Icc (-1 : ℝ) 1 := abs_le.mp hp
  have hqI : q ∈ Icc (-1 : ℝ) 1 := abs_le.mp hq
  rcases no_double_failure heps hx2 hy2 hp hq hrootq hrootp'
      (hb p hpI) (hb q hqI) (hpadding p hpI q hqI) with hu | hl
  · left
    refine ⟨q, 1 - t + eps * x * q, hq, hrho, ?_, ?_, ?_⟩
    · simpa only [hcap q hqI] using hu
    · unfold RadialCaps.G
      nlinarith only [hrootq]
    · ring
  · right
    refine ⟨p, 1 + t - eps * y * p, hp, ?_, ?_, ?_, ?_⟩
    · nlinarith only [hsigma]
    · simpa only [hcap p hpI] using hl
    · unfold RadialCaps.G
      nlinarith only [hrootp']
    · ring

theorem padding_covers {h eps : ℝ} {R b : ℝ → ℝ}
    (heps : 0 < eps)
    (hcap : ∀ r ∈ Icc (-1 : ℝ) 1, R r = 1 + eps ^ 2 * (RadialCaps.H r + b r))
    (hb : ∀ r ∈ Icc (-1 : ℝ) 1, 0 ≤ b r)
    (hpadding : ∀ p ∈ Icc (-1 : ℝ) 1, ∀ q ∈ Icc (-1 : ℝ) 1,
      9 * eps ≤ b p + b q) :
    RadialPairedSweep.tetrahedron h ⊆
      RadialPairedSweep.upperSweep h eps R ∪ RadialPairedSweep.lowerSweep h eps R := by
  rintro z ⟨x, y, t, hx, hy, rfl⟩
  rcases padding_coverage heps hcap hb hpadding hx hy with hu | hl
  · obtain ⟨q, rho, hq, hrho, hR, hyrep, htrep⟩ := hu
    left
    refine ⟨q, abs_le.mp hq, rho, ⟨hrho, hR⟩, x, ?_, ?_⟩
    · linarith only [hx, hy, abs_nonneg y]
    · rw [← hyrep, ← htrep]
  · obtain ⟨p, sigma, hp, hsigma, hR, hxrep, htrep⟩ := hl
    right
    refine ⟨p, abs_le.mp hp, sigma, ⟨hsigma, hR⟩, y, ?_, ?_⟩
    · linarith only [hx, hy, abs_nonneg x]
    · rw [← hxrep, ← htrep]

theorem linear_covers {h beta eps : ℝ} (hbeta : 0 ≤ beta)
    (heps : 0 < eps) (hsmall : eps ≤ 2 * beta / 9) :
    RadialPairedSweep.tetrahedron h ⊆
      RadialPairedSweep.upperSweep h eps (RadialCaps.linearCap beta eps) ∪
        RadialPairedSweep.lowerSweep h eps (RadialCaps.linearCap beta eps) := by
  apply padding_covers (b := fun _ => beta) heps
  · intro r hr
    rfl
  · intro r hr
    exact hbeta
  · intro p hp q hq
    linarith only [hsmall]

theorem cubic_covers {h c eps : ℝ} (hc : (9 : ℝ) / 2 ≤ c) (heps : 0 < eps) :
    RadialPairedSweep.tetrahedron h ⊆
      RadialPairedSweep.upperSweep h eps (RadialCaps.cubicCap c eps) ∪
        RadialPairedSweep.lowerSweep h eps (RadialCaps.cubicCap c eps) := by
  apply padding_covers (b := fun _ => c * eps) heps
  · intro r hr
    unfold RadialCaps.cubicCap
    ring
  · intro r hr
    exact mul_nonneg (by linarith only [hc]) heps.le
  · intro p hp q hq
    nlinarith only [mul_le_mul_of_nonneg_right hc heps.le]

theorem fractional_power (eps : ℝ) (heps : 0 < eps) :
    eps ^ (5 / 2 : ℝ) = eps ^ 2 * Real.sqrt eps := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add heps]
  rw [← Real.sqrt_eq_rpow]
  norm_num

theorem fractional_covers {h c eps : ℝ} (hc : 0 < c) (heps : 0 < eps)
    (hsmall : eps ≤ (2 * c / 9) ^ 2) :
    RadialPairedSweep.tetrahedron h ⊆
      RadialPairedSweep.upperSweep h eps (RadialCaps.fractionalCap c eps) ∪
        RadialPairedSweep.lowerSweep h eps (RadialCaps.fractionalCap c eps) := by
  have hsqrt : Real.sqrt eps ≤ 2 * c / 9 := by
    nlinarith only [Real.sq_sqrt heps.le, Real.sqrt_nonneg eps, hc, hsmall]
  apply padding_covers (b := fun _ => c * Real.sqrt eps) heps
  · intro r hr
    unfold RadialCaps.fractionalCap
    rw [fractional_power eps heps]
    ring
  · intro r hr
    exact mul_nonneg hc.le (Real.sqrt_nonneg eps)
  · intro p hp q hq
    have hh := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg eps)
    nlinarith only [hh, Real.sq_sqrt heps.le]

end CylinderCovering.RadialCapCoverage

end

end OAI
