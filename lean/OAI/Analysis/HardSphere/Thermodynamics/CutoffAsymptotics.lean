import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.PathCutoff

lemma stretched_exp_decay (p : ℝ) {b q : ℝ} (hb : 0<b) (hq : 0<q) :
    Tendsto (fun D:ℝ ↦ D^p*Real.exp (-b*D^q)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p/q) b hb).comp
    (tendsto_rpow_atTop hq)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  dsimp
  rw [←Real.rpow_mul hD]
  congr 2
  field_simp

def scalarRegularBound (C M c a b D : ℝ) : ℝ :=
  C*D^2*M*Real.exp (-(c/1296)*D^(1/6:ℝ))+
    Real.exp (-(a/8)*D)+2*M*Real.exp (-(c*b^2/82944)*D^(1/3:ℝ))

lemma scalarRegularBound_decay (p C M : ℝ) {c a b : ℝ}
    (hc : 0<c) (ha : 0<a) (hb : 0<b) :
    Tendsto (fun D:ℝ ↦ D^p*scalarRegularBound C M c a b D) atTop (𝓝 0) := by
  have h₁ := (stretched_exp_decay (p+2) (by positivity : (0:ℝ)<c/1296)
    (by norm_num : (0:ℝ)<1/6)).const_mul (C*M)
  have h₂ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (a/8) (by positivity)
  have h₃ := (stretched_exp_decay p (by positivity : (0:ℝ)<c*b^2/82944)
    (by norm_num : (0:ℝ)<1/3)).const_mul (2*M)
  have ht := (h₁.add h₂).add h₃
  simp only [mul_zero,zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
  dsimp [scalarRegularBound]
  rw [Real.rpow_add hD,Real.rpow_two]
  ring

end HardSphere.PathCutoff

end

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace HardSphere.PathCutoff

lemma regularScale_mesh {D : ℝ} (hD : 0<D) :
    (D^(1/12:ℝ)/36)^2=D^(1/6:ℝ)/1296 := by
  rw [div_pow,←Real.rpow_natCast,←Real.rpow_mul hD.le]
  norm_num

lemma regularScale_endpoint {D b : ℝ} (hD : 0<D) :
    ((b*D^(-(1/3:ℝ))/8)/(36*Real.sqrt (D⁻¹)))^2=
      b^2/82944*D^(1/3:ℝ) := by
  rw [div_pow,mul_pow,div_pow,mul_pow,Real.sq_sqrt (by positivity : 0≤D⁻¹)]
  have hx : (D^(-(1/3:ℝ)))^2=D^(-(2/3:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num
  rw [hx]
  have he : D^(-(2/3:ℝ))*D=D^(1/3:ℝ) := by
    calc
      _ = D^(-(2/3:ℝ))*D^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hD]; norm_num
  calc
    _ = b^2/82944*(D^(-(2/3:ℝ))*D) := by field_simp; ring
    _ = _ := by rw [he]

lemma regularScale_denominator {D : ℝ} (hD : 1≤D) :
    (1+D^(1/12:ℝ))^3≤8*D := by
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hp : 1≤D^(1/12:ℝ) := Real.one_le_rpow hD (by norm_num)
  have hsum : 1+D^(1/12:ℝ)≤2*D^(1/12:ℝ) := by linarith
  have hp3 : (D^(1/12:ℝ))^3=D^(1/4:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD0.le]
    norm_num
  calc
    _ ≤ (2*D^(1/12:ℝ))^3 := pow_le_pow_left₀ (by positivity) hsum 3
    _ = 8*D^(1/4:ℝ) := by rw [mul_pow,hp3]; norm_num
    _ ≤ 8*D := by
      gcongr
      simpa using Real.rpow_le_rpow_of_exponent_le hD (by norm_num : (1/4:ℝ)≤1)

lemma regularScale_majorant {D C M c a b : ℝ} {m : ℕ}
    (hD : 1≤D) (_ : 0≤C) (hM : 0≤M) (_ : 0≤c) (ha : 0≤a)
    (hmlo : a*D^2≤(m:ℝ)) (hmhi : (m:ℝ)≤C*D^2) :
    (m:ℝ)*(M*Real.exp (-c*(D^(1/12:ℝ)/36)^2))+
      Real.exp (-(m:ℝ)/((1+D^(1/12:ℝ))^3))+
      2*(M*Real.exp (-c*((b*D^(-(1/3:ℝ))/8)/(36*Real.sqrt (D⁻¹)))^2))≤
        scalarRegularBound C M c a b D := by
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hden : 0<(1+D^(1/12:ℝ))^3 := by positivity
  have hm : a/8*D≤(m:ℝ)/((1+D^(1/12:ℝ))^3) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (a/8*D)*(8*D) := mul_le_mul_of_nonneg_left (regularScale_denominator hD) (by positivity)
      _ = a*D^2 := by ring
      _ ≤ _ := hmlo
  rw [regularScale_mesh hD0,regularScale_endpoint hD0]
  unfold scalarRegularBound
  have hexp₁ : -c*(D^(1/6:ℝ)/1296)=-(c/1296)*D^(1/6:ℝ) := by ring
  have hexp₂ : -c*(b^2/82944*D^(1/3:ℝ))=-(c*b^2/82944)*D^(1/3:ℝ) := by ring
  rw [hexp₁,hexp₂]
  apply add_le_add _ (le_of_eq (by ring))
  apply add_le_add _ _
  · calc
      _ ≤ (C*D^2)*(M*Real.exp (-(c/1296)*D^(1/6:ℝ))) := mul_le_mul_of_nonneg_right hmhi (by positivity)
      _ = _ := by ring
  · apply Real.exp_le_exp.mpr
    rw [neg_div]
    nlinarith

end HardSphere.PathCutoff

end

end OAI
