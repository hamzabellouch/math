import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedRicci.WeightedMongeAmpereEnergy

namespace OAI

/-! Monge Ampere Power Energy. -/

section

 
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth

private def powerBase (t : ℝ) : ℝ := 1+t^2
private lemma powerBase_pos (t : ℝ) : 0 < powerBase t := by dsimp [powerBase]; positivity
private lemma powerBase_smooth : ContDiff ℝ ∞ powerBase := by unfold powerBase; fun_prop
private lemma powerBase_deriv (t : ℝ) : HasDerivAt powerBase (2*t) t := by
  convert (hasDerivAt_const t (1:ℝ)).add ((hasDerivAt_id t).pow 2) using 1 <;> first | rfl | norm_num [powerBase]

def moserTest (p t : ℝ) : ℝ := t * powerBase t ^ (p/2-1)
def moserPower (p t : ℝ) : ℝ := powerBase t ^ (p/4)

lemma moserTest_smooth (p : ℝ) : ContDiff ℝ ∞ (moserTest p) :=
  contDiff_id.mul (powerBase_smooth.rpow_const_of_ne (fun t => ne_of_gt (powerBase_pos t)))
lemma moserPower_smooth (p : ℝ) : ContDiff ℝ ∞ (moserPower p) :=
  powerBase_smooth.rpow_const_of_ne (fun t => ne_of_gt (powerBase_pos t))

lemma moserTest_deriv (p t : ℝ) : deriv (moserTest p) t =
    powerBase t ^ (p/2-1) + t*((p/2-1)*powerBase t ^ (p/2-1-1)*(2*t)) := by
  have h := ((hasDerivAt_id t).mul ((powerBase_deriv t).rpow_const (p:=p/2-1) (Or.inl (ne_of_gt (powerBase_pos t))))).deriv
  change deriv (moserTest p) t = _ at h
  rw [h]
  dsimp only [id_eq]
  ring

lemma moserPower_deriv (p t : ℝ) : deriv (moserPower p) t =
    (p/4)*powerBase t ^ (p/4-1)*(2*t) := by
  have h := ((powerBase_deriv t).rpow_const (p:=p/4) (Or.inl (ne_of_gt (powerBase_pos t)))).deriv
  change deriv (moserPower p) t = _ at h
  rw [h]
  ring

lemma moserTest_deriv_lower {p : ℝ} (hp : 2 ≤ p) (t : ℝ) :
    powerBase t ^ (p/2-1) ≤ deriv (moserTest p) t := by
  rw [moserTest_deriv]
  have ha : 0 ≤ p/2-1 := by linarith
  have hb := Real.rpow_nonneg (powerBase_pos t).le (p/2-1-1)
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg t)]

lemma moserTest_deriv_nonneg {p : ℝ} (hp : 2 ≤ p) (t : ℝ) :
    0 ≤ deriv (moserTest p) t :=
  (Real.rpow_nonneg (powerBase_pos t).le _).trans (moserTest_deriv_lower hp t)

lemma moserPower_deriv_sq_le {p : ℝ} (hp : 2 ≤ p) (t : ℝ) :
    (deriv (moserPower p) t)^2 ≤ (p^2/4) * deriv (moserTest p) t := by
  have hb := powerBase_pos t
  have he : (powerBase t ^ (p/4-1))^2 = powerBase t ^ (p/2-2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    congr 1; ring
  have he' : powerBase t ^ (p/2-2) * powerBase t = powerBase t ^ (p/2-1) := by
    conv_lhs => rhs; rw [← Real.rpow_one (powerBase t)]
    rw [← Real.rpow_add hb]
    congr 1; ring
  calc
    _ = (p^2/4) * (powerBase t ^ (p/2-2) * t^2) := by rw [moserPower_deriv, mul_pow, mul_pow, he]; ring
    _ ≤ (p^2/4) * (powerBase t ^ (p/2-2) * powerBase t) := by
      gcongr
      dsimp [powerBase]; linarith
    _ = (p^2/4) * powerBase t ^ (p/2-1) := by rw [he']
    _ ≤ _ := mul_le_mul_of_nonneg_left (moserTest_deriv_lower hp t) (by positivity)

lemma abs_moserTest_le (p t : ℝ) : |moserTest p t| ≤ (moserPower p t)^2 := by
  have hb := powerBase_pos t
  have hab : |t| ≤ powerBase t := by
    dsimp [powerBase]
    nlinarith [sq_nonneg (|t|-1), sq_abs t]
  have he : powerBase t * powerBase t ^ (p/2-1) = (moserPower p t)^2 := by
    unfold moserPower
    rw [← Real.rpow_two, ← Real.rpow_mul hb.le]
    conv_lhs => lhs; rw [← Real.rpow_one (powerBase t)]
    rw [← Real.rpow_add hb]
    congr 1; ring
  calc
    _ = |t| * powerBase t ^ (p/2-1) := by rw [moserTest, abs_mul, abs_of_nonneg (Real.rpow_nonneg hb.le _)]
    _ ≤ powerBase t * powerBase t ^ (p/2-1) := mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hb.le _)
    _ = _ := he

lemma moserPower_sq (p t : ℝ) : (moserPower p t)^2 = (1+t^2)^(p/2) := by
  unfold moserPower powerBase
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1+t^2)]
  congr 1; ring

lemma moserPower_rpow (p q t : ℝ) : ‖moserPower p t‖^q = (1+t^2)^(p*q/4) := by
  unfold moserPower powerBase
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1+t^2)]
  congr 1; ring

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}
namespace KaehlerMetric

theorem mongeAmpere_power_energy (g : KaehlerMetric A) (hd : 0 < d)
    (D : ℝ) (_hD : 0 ≤ D) (φ : SmoothRealFunction A) (hp : g.PositivePotential φ)
    (hρ : ∀ x, |1 - (g.potentialDensity φ).value x| ≤ D)
    (p : ℝ) (hpow : 2 ≤ p) :
    g.integral (g.energy (φ.compose (moserPower p) (moserPower_smooth p))
      (φ.compose (moserPower p) (moserPower_smooth p))).value ≤
        (p^2/4) * (D / (1/2:ℝ)^d) * g.integral (fun x => (moserPower p (φ.value x))^2) := by
  let F := moserTest p
  let U := moserPower p
  have hF := moserTest_smooth p
  have hU := moserPower_smooth p
  have hma := g.mongeAmpere_weighted_energy φ hp hd F hF (moserTest_deriv_nonneg hpow)
  have hFc : Continuous (fun x => F (φ.value x)) := hF.continuous.comp φ.continuous
  have hUc : Continuous (fun x => (U (φ.value x))^2) := (hU.continuous.comp φ.continuous).pow 2
  have hbound : g.integral (fun x => F (φ.value x)) -
      g.integral (fun x => F (φ.value x) * (g.potentialDensity φ).value x) ≤
        D * g.integral (fun x => (U (φ.value x))^2) := by
    rw [← g.integral_sub hFc (hFc.fun_mul (g.potentialDensity φ).continuous), ← g.integral_const_mul]
    apply g.integral_mono (hFc.sub (hFc.fun_mul (g.potentialDensity φ).continuous)) (continuous_const.fun_mul hUc)
    intro x
    calc
      _ = F (φ.value x) * (1-(g.potentialDensity φ).value x) := by simp only [Pi.sub_apply]; ring
      _ ≤ |F (φ.value x) * (1-(g.potentialDensity φ).value x)| := le_abs_self _
      _ = |F (φ.value x)| * |1-(g.potentialDensity φ).value x| := abs_mul _ _
      _ ≤ (U (φ.value x))^2 * D := mul_le_mul (abs_moserTest_le p _) (hρ x) (abs_nonneg _) (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hE : g.integral (g.energy (φ.compose U hU) (φ.compose U hU)).value ≤
      (p^2/4) * g.integral (fun x => deriv F (φ.value x) * (g.energy φ φ).value x) := by
    rw [← g.integral_const_mul]
    apply g.integral_mono (g.energy _ _).continuous
      (continuous_const.fun_mul (((hF.continuous_deriv (by simp)).comp φ.continuous).fun_mul (g.energy φ φ).continuous))
    intro x
    rw [g.energy_comp_self]
    have hh := mul_le_mul_of_nonneg_right (moserPower_deriv_sq_le hpow (φ.value x)) (g.energy_nonneg φ x)
    simpa only [U, Function.comp_apply, mul_assoc] using hh
  have hc : 0 < (1/2:ℝ)^d := by positivity
  have hma' : g.integral (fun x => deriv F (φ.value x) * (g.energy φ φ).value x) ≤
      (D / (1/2:ℝ)^d) * g.integral (fun x => (U (φ.value x))^2) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hma.trans hbound
  exact hE.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hma' (show 0 ≤ p^2/4 by positivity))

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
