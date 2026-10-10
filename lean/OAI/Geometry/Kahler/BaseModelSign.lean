import OAI.Geometry.Kahler.BaseRadialPatch

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def modelIntegrand (a ε ρ : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)-
    f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε

def modelMean (a ε ρ R : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ y in 0..R, modelIntegrand a ε ρ f y

lemma modelIntegrand_continuous {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => modelIntegrand a p.1.1 p.1.2 f p.2) := by
  have hL : Continuous (fun p : (ℝ × ℝ) × ℝ => logFactor (a*p.1.2*Real.exp (-p.2)) p.1.1) :=
    logFactor_continuous.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ => (a*p.1.2*Real.exp (-p.2),p.1.1)) from by fun_prop)
  have hD : Continuous (fun p : (ℝ × ℝ) × ℝ => Real.log (1+p.1.1^2)) := by
    apply Continuous.log
    · fun_prop
    · intro p
      positivity
  have hN : Continuous (fun p : (ℝ × ℝ) × ℝ => f p.2*(a*p.1.2*Real.exp (-p.2))) :=
    (hf.comp continuous_snd).mul (show Continuous (fun p : (ℝ × ℝ) × ℝ => a*p.1.2*Real.exp (-p.2)) from by fun_prop)
  exact ((hL.log (fun p => (logFactor_pos _ _).ne')).sub hD).sub
    (hN.div hL (fun p => (logFactor_pos _ _).ne'))

lemma modelIntegrand_continuous_y {f : ℝ → ℝ} (hf : Continuous f) (a ε ρ : ℝ) :
    Continuous (modelIntegrand a ε ρ f) := by
  have hc : Continuous (fun y : ℝ => ((ε,ρ),y)) := by fun_prop
  exact Continuous.comp (g := fun p : (ℝ × ℝ) × ℝ => modelIntegrand a p.1.1 p.1.2 f p.2)
    (f := fun y : ℝ => ((ε,ρ),y)) (modelIntegrand_continuous hf a) hc

lemma RadialProfiles.log_lt_cutoff {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) : Real.log a < p.cutoff := by
  by_contra h
  have hp := p.plateau (Real.log a) ⟨(Real.log_pos ha).le,le_rfl⟩
  have ht := (p.tail (Real.log a) (le_of_not_gt h)).1
  linarith [p.s_pos]

lemma modelIntegrand_zero_low {a y : ℝ} (ha : 0 < a) (hy : y ≤ Real.log a) (f : ℝ → ℝ) :
    modelIntegrand a 0 1 f y = 2*(Real.log a-y)-f y*Real.exp (y-Real.log a) := by
  have hq : a*Real.exp (-y)=Real.exp (Real.log a-y) := by rw [Real.exp_sub,Real.exp_log ha,Real.exp_neg,div_eq_mul_inv]
  have hge : 1 ≤ a*Real.exp (-y) := by rw [hq]; exact Real.one_le_exp_iff.mpr (by linarith)
  have hsq : 1 ≤ (a*Real.exp (-y))^2 := by nlinarith
  unfold modelIntegrand
  simp only [mul_one,logFactor_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.log_one,sub_zero,max_eq_right hsq]
  rw [hq,Real.log_pow,Real.log_exp]
  have he : Real.exp (y-Real.log a)=(Real.exp (Real.log a-y))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  rw [he]
  field_simp
  ring

lemma modelIntegrand_zero_high {a y : ℝ} (ha : 0 < a) (hy : Real.log a ≤ y) (f : ℝ → ℝ) :
    modelIntegrand a 0 1 f y = -f y*(a*Real.exp (-y)) := by
  have hq : a*Real.exp (-y)=Real.exp (Real.log a-y) := by rw [Real.exp_sub,Real.exp_log ha,Real.exp_neg,div_eq_mul_inv]
  have hle : a*Real.exp (-y) ≤ 1 := by rw [hq]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hpos : 0 ≤ a*Real.exp (-y) := by positivity
  have hsq : (a*Real.exp (-y))^2 ≤ 1 := by nlinarith
  unfold modelIntegrand
  simp only [mul_one,logFactor_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.log_one,sub_zero,max_eq_left hsq,div_one,zero_sub,neg_mul]

lemma RadialProfiles.model_weight_zero {a : ℝ} (p : RadialProfiles a) :
    (∫ y in 0..p.R, p.f y*(a*Real.exp (-y)))=0 := by
  have hh := weight_profile_integral p.smooth_f.continuous p.smooth_b.continuous p.ode p.R_pos.le p.b_zero
    ((p.tail p.R p.cutoff_lt.le).2) 1
  simp only [sub_self,zero_mul,add_zero,neg_one_mul] at hh
  have he : (fun y => p.f y*(a*Real.exp (-y))) = fun y => a*(Real.exp (-y)*p.f y) := by ext y; ring
  rw [he,intervalIntegral.integral_const_mul,hh,mul_zero]

lemma model_small_integral {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) :
    (∫ y in 0..Real.log a, modelIntegrand a 0 1 p.f y+p.f y*(a*Real.exp (-y))) =
      (Real.log a)^2-2*p.s*(Real.cosh (Real.log a)-1) := by
  let α := Real.log a
  have hα : 0 < α := Real.log_pos ha
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have he : ∀ y ∈ uIcc 0 α, modelIntegrand a 0 1 p.f y+p.f y*(a*Real.exp (-y)) =
      2*(α-y)+p.s*(Real.exp (y-α)-Real.exp (α-y)) := by
    intro y hy
    rw [uIcc_of_le hα.le] at hy
    rw [modelIntegrand_zero_low ha0 hy.2,p.plateau y hy]
    have hq : a*Real.exp (-y)=Real.exp (α-y) := by
      dsimp [α]
      rw [Real.exp_sub,Real.exp_log ha0,Real.exp_neg,div_eq_mul_inv]
    rw [hq]
    dsimp [α]
    ring
  rw [intervalIntegral.integral_congr he]
  have hd : ∀ y, HasDerivAt (fun y => 2*α*y-y^2+p.s*(Real.exp (y-α)+Real.exp (α-y)))
    (2*(α-y)+p.s*(Real.exp (y-α)-Real.exp (α-y))) y := by
    intro y
    convert! (((hasDerivAt_id y).const_mul (2*α)).sub ((hasDerivAt_id y).pow 2)).add
      ((((hasDerivAt_id y).sub_const α).exp).add (((hasDerivAt_const y α).sub (hasDerivAt_id y)).exp) |>.const_mul p.s) using 1; dsimp; ring
  have hc : Continuous (fun y : ℝ => 2*(α-y)+p.s*(Real.exp (y-α)-Real.exp (α-y))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable 0 α)]
  simp only [sub_self,Real.exp_zero,mul_zero,pow_two,sub_zero,zero_sub]
  rw [Real.cosh_eq]
  dsimp [α]
  ring

lemma model_large_integral {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) :
    (∫ y in Real.log a..p.R, modelIntegrand a 0 1 p.f y+p.f y*(a*Real.exp (-y)))=0 := by
  have hαR : Real.log a < p.R := (p.log_lt_cutoff ha).trans p.cutoff_lt
  calc
    _ = ∫ y in Real.log a..p.R, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hαR.le] at hy
      dsimp only
      rw [modelIntegrand_zero_high (lt_trans zero_lt_one ha) hy.1]
      ring
    _ = 0 := by simp

lemma modelMean_zero {a : ℝ} (ha : 1 < a) (p : RadialProfiles a) :
    modelMean a 0 1 p.R p.f = (Real.log a)^2-2*p.s*(Real.cosh (Real.log a)-1) := by
  let M := modelIntegrand a 0 1 p.f
  let F : ℝ → ℝ := fun y => p.f y*(a*Real.exp (-y))
  have hM : Continuous M := modelIntegrand_continuous_y p.smooth_f.continuous a 0 1
  have hF : Continuous F := by
    apply Continuous.mul p.smooth_f.continuous
    fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hM.add hF).intervalIntegrable 0 (Real.log a)) ((hM.add hF).intervalIntegrable (Real.log a) p.R)
  change (∫ y in 0..Real.log a, M y+F y)+(∫ y in Real.log a..p.R, M y+F y)=(∫ y in 0..p.R, M y+F y) at hadd
  rw [model_small_integral ha p,model_large_integral ha p,add_zero,
    intervalIntegral.integral_add (hM.intervalIntegrable 0 p.R) (hF.intervalIntegrable 0 p.R),
    p.model_weight_zero,add_zero] at hadd
  exact hadd.symm

end PinchedHartogs.BaseConstruction

end

end OAI
