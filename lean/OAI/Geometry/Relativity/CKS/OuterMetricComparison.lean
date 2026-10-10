import OAI.Geometry.Relativity.CKS.CollarMetricRealization
import OAI.Geometry.Relativity.CKS.CollarMetricComparison

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

def outerComparisonFactor (M R : ℝ) : ℝ := 1/(1+2*M/R^3)

lemma outerComparisonFactor_pos {M R : ℝ} (hM : 0 ≤ M) (hR : 0<R) :
    0 < outerComparisonFactor M R := by unfold outerComparisonFactor; positivity

lemma outerComparisonFactor_le_one {M R : ℝ} (hM : 0 ≤ M) (hR : 0<R) :
    outerComparisonFactor M R ≤ 1 := by
  unfold outerComparisonFactor
  apply (div_le_one (by positivity)).mpr
  have : 0 ≤ 2*M/R^3 := by positivity
  linarith

lemma outerComparisonFactor_tendsto (M : ℝ) : Tendsto (outerComparisonFactor M) atTop (𝓝 1) := by
  have hp : Tendsto (fun R : ℝ => R^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun R : ℝ => (R^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hp
  have hm : Tendsto (fun R : ℝ => 2*M/R^3) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hz.const_mul (2*M)
  have hd : Tendsto (fun R : ℝ => 1+2*M/R^3) atTop (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using hm.const_add (1:ℝ)
  have hh := hd.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  change Tendsto (fun R : ℝ => 1/(1+2*M/R^3)) atTop (𝓝 1)
  simpa only [one_div,inv_one] using hh

lemma outer_radicand_positive {r F v M : ℝ} (hr : 0<r) (hF : |F| ≤ M) (hsmall : 4*M ≤ r) :
    0 < 1+v^2-2*F/r := by
  have hF' : F ≤ M := (le_abs_self F).trans hF
  have hf : 2*F/r ≤ 1/2 := (div_le_iff₀ hr).mpr (by linarith)
  nlinarith [sq_nonneg v]

lemma outer_radial_coefficient_lower {r R F v M : ℝ}
    (hR : 1 ≤ R) (hr : R ≤ r) (hM : 0 ≤ M) (hF : |F| ≤ M)
    (hv0 : 0 ≤ v) (hv : v ≤ r) (hpos : 0 < 1+v^2-2*F/r) :
    outerComparisonFactor M R ≤ (1+r^2)/(1+v^2-2*F/r) := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hrp : 0<r := hRp.trans_le hr
  have hbase : 0<1+r^2 := by positivity
  have hden : 0<1+2*M/R^3 := by positivity
  have hF' : -M ≤ F := (abs_le.mp hF).1
  have hv2 : v^2 ≤ r^2 := pow_le_pow_left₀ hv0 hv 2
  have hR3 : R^3 ≤ r^3 := pow_le_pow_left₀ hRp.le hr 3
  have hrad : R^3 ≤ r*(1+r^2) := by nlinarith
  have hratio : 2*M/r ≤ (1+r^2)*(2*M/R^3) := by
    apply (div_le_iff₀ hrp).mpr
    have he : (1+r^2)*(2*M/R^3)*r=(2*M)*(r*(1+r^2))/R^3 := by ring
    rw [he]
    apply (le_div_iff₀ (pow_pos hRp 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrad (show 0 ≤ 2*M by positivity)]
  have hupper : 1+v^2-2*F/r ≤ (1+r^2)*(1+2*M/R^3) := by
    have hFdiv : -(2*F/r) ≤ 2*M/r := by
      simpa only [neg_div] using div_le_div_of_nonneg_right (show -(2*F) ≤ 2*M by linarith) hrp.le
    nlinarith
  unfold outerComparisonFactor
  apply (div_le_div_iff₀ hden hpos).mpr
  nlinarith

lemma radialNormalize_round {r u : ℝ} (hr : r ≠ 0) (q : Mat) :
    radialNormalize r (foliationMetric u (r^2 • q) 0)=metricBlock ((1+r^2)/u^2) 0 q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialNormalize,radialScale,foliationMetric,metricBlock,Matrix.of_apply,Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring_nf
  all_goals rw [Real.sq_sqrt (show 0 ≤ 1+r^2 by positivity)]
  all_goals ring

lemma quadratic3_block_diagonal (a : ℝ) (q : Mat) (v : Fin 3 → ℝ) :
    quadratic3 (metricBlock a 0 q) v=a*(v 0)^2+
      (star (fun i : Fin 2 => v i.succ)) ⬝ᵥ (q *ᵥ (fun i => v i.succ)) := by
  simp [quadratic3,metricBlock,Matrix.of_apply,dotProduct,mulVec,Fin.sum_univ_three,Fin.sum_univ_two]
  ring

lemma outer_metric_lower {r R F v M : ℝ} {q : Mat}
    (hR : 1 ≤ R) (hr : R ≤ r) (hM : 0 ≤ M) (hF : |F| ≤ M)
    (hv0 : 0 ≤ v) (hv : v ≤ r) (hpos : 0 < 1+v^2-2*F/r) (hq : q.PosDef) :
    ∀ w : Fin 3 → ℝ,
    outerComparisonFactor M R*quadratic3 (metricBlock 1 0 q) w ≤
      quadratic3 (radialNormalize r (foliationMetric (Real.sqrt (1+v^2-2*F/r)) (r^2 • q) 0)) w := by
  have hrp : 0<r := (zero_lt_one.trans_le hR).trans_le hr
  have hc := outerComparisonFactor_le_one hM (zero_lt_one.trans_le hR)
  have hrad := outer_radial_coefficient_lower hR hr hM hF hv0 hv hpos
  intro w
  rw [radialNormalize_round hrp.ne',Real.sq_sqrt hpos.le,quadratic3_block_diagonal,quadratic3_block_diagonal]
  have hq0 := hq.posSemidef.dotProduct_mulVec_nonneg (fun i : Fin 2 => w i.succ)
  nlinarith [mul_le_mul_of_nonneg_right hrad (sq_nonneg (w 0)),
    mul_le_mul_of_nonneg_right hc hq0]

end
end CKSAngularGeometry

end

end OAI
