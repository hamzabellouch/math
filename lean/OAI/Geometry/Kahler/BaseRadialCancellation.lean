import OAI.Geometry.Kahler.BaseAdaptedHopf

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma log_sqrt_power {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (Real.sqrt t)^n = Real.exp ((n:ℝ)/2*Real.log t) := by
  rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos ht,← Real.exp_nat_mul]
  congr 1
  ring

lemma interval_indicator_above {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (g : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, if a<t then g t else 0) = ∫ t in a..1, g t := by
  classical
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),intervalIntegral.integral_of_le ha1]
  change (∫ t in Ioc (0:ℝ) 1, (Ioi a).indicator g t) = _
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi a ∩ Ioc (0:ℝ) 1 = Ioc a 1 := by
    ext t
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    constructor
    · rintro ⟨ht,_,ht1⟩; exact ⟨ht,ht1⟩
    · rintro ⟨ht,ht1⟩; exact ⟨ht,lt_of_le_of_lt ha ht,ht1⟩
  rw [hset]

lemma radial_profile_moment {f b : ℝ → ℝ} (hf : Continuous f) (hb : Continuous b)
    (hode : ∀ y, HasDerivAt b (b y+f y) y) {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    (hzero : b 0=0) (htail : b R=0) (n : ℕ) :
    (∫ t in (0:ℝ)..1, if Real.exp (-2*R/k)<t then
      ((t⁻¹*(Real.sqrt t)^n*(f (-k/2*Real.log t)+(1-(n:ℝ)/k)*b (-k/2*Real.log t)):ℝ):ℂ) else 0)=0 := by
  let F : ℝ → ℂ := fun y => ((Real.exp (-(n:ℝ)/k*y)*(f y+(1-(n:ℝ)/k)*b y):ℝ):ℂ)
  have hF : Continuous F := by unfold F; fun_prop
  have ha : Real.exp (-2*R/k) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hk.le)
  rw [interval_indicator_above (Real.exp_pos _).le ha]
  have he : (∫ t in Real.exp (-2*R/k)..1,
      ((t⁻¹*(Real.sqrt t)^n*(f (-k/2*Real.log t)+(1-(n:ℝ)/k)*b (-k/2*Real.log t)):ℝ):ℂ)) =
      ∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • F (-k/2*Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le ha] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht.1
    dsimp only
    rw [log_sqrt_power ht0 n]
    unfold F
    have hex : -(n:ℝ)/k*(-k/2*Real.log t)=(n:ℝ)/2*Real.log t := by field_simp
    rw [hex]
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he,log_radial_substitution hk hR hF]
  have hi : (∫ y in 0..R, F y)=0 := by
    unfold F
    rw [intervalIntegral.integral_ofReal]
    rw [show -(n:ℝ)/k = -((n:ℝ)/k) by ring,
      weight_profile_integral hf hb hode hR.le hzero htail ((n:ℝ)/k)]
    rfl
  rw [hi,smul_zero]

end PinchedHartogs.BaseConstruction

end

end OAI
