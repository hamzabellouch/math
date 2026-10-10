import OAI.Geometry.Relativity.CKS.CollarMetricRealization
import OAI.Geometry.Relativity.CKS.CollarMetricComparison

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

def comparisonFactor (C B κ R : ℝ) : ℝ := (1-3*C/(κ*R^3))/(1+12*B/(κ*R^3))

lemma comparisonFactor_nonneg {C B κ R : ℝ} (hB : 0 ≤ B) (hκ : 0<κ) (hR : 0<R)
    (hsmall : 3*C ≤ κ*R^3) : 0 ≤ comparisonFactor C B κ R := by
  unfold comparisonFactor
  apply div_nonneg
  · exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hsmall)
  · positivity

lemma comparisonFactor_le_one {C B κ R : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hκ : 0<κ) (hR : 0<R) : comparisonFactor C B κ R ≤ 1 := by
  unfold comparisonFactor
  have hd : 0<1+12*B/(κ*R^3) := by positivity
  apply (div_le_one hd).mpr
  have hc : 0 ≤ 3*C/(κ*R^3) := by positivity
  have hb : 0 ≤ 12*B/(κ*R^3) := by positivity
  linarith

lemma comparisonFactor_tendsto (C B κ : ℝ) :
    Tendsto (comparisonFactor C B κ) atTop (𝓝 1) := by
  have hp : Tendsto (fun R : ℝ => R^3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun R : ℝ => (R^3)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hp
  have hc : Tendsto (fun R : ℝ => 3*C/(κ*R^3)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,_root_.mul_inv_rev,mul_zero,zero_mul,mul_assoc,mul_left_comm,mul_comm] using
      (tendsto_const_nhds.mul hz : Tendsto (fun R : ℝ => (3*C/κ)*(R^3)⁻¹) atTop (𝓝 ((3*C/κ)*0)))
  have hb : Tendsto (fun R : ℝ => 12*B/(κ*R^3)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,_root_.mul_inv_rev,mul_zero,zero_mul,mul_assoc,mul_left_comm,mul_comm] using
      (tendsto_const_nhds.mul hz : Tendsto (fun R : ℝ => (12*B/κ)*(R^3)⁻¹) atTop (𝓝 ((12*B/κ)*0)))
  have hone : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hnum : Tendsto (fun R : ℝ => 1-3*C/(κ*R^3)) atTop (𝓝 (1:ℝ)) := by
    simpa only [sub_zero] using hone.sub hc
  have hden : Tendsto (fun R : ℝ => 1+12*B/(κ*R^3)) atTop (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using hone.add hb
  change Tendsto (fun R : ℝ => (1-3*C/(κ*R^3))/(1+12*B/(κ*R^3))) atTop (𝓝 1)
  convert hnum.div hden (by norm_num : (1:ℝ) ≠ 0) using 1
  norm_num

lemma uniform_error {C r R : ℝ} (hC : 0 ≤ C) (hR : 0<R) (hr : R ≤ r) : C/r^3 ≤ C/R^3 := by
  exact div_le_div_of_nonneg_left hC (pow_pos hR 3) (pow_le_pow_left₀ hR.le hr 3)

lemma metric_comparison_uniform {G g H : AmbientMat} {C B κ r R : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hκ : 0<κ) (hR : 0<R) (hr : R ≤ r)
    (hsmall : 3*C ≤ κ*R^3)
    (hG : ‖G-H‖ ≤ C/r^3) (hg : ‖g-H‖ ≤ 4*B/r^3)
    (hbg : ∀ v : Fin 3 → ℝ, κ*(∑ i, (v i)^2) ≤ quadratic3 H v) :
    ∀ v, comparisonFactor C B κ R*quadratic3 g v ≤ quadratic3 G v := by
  have hGc := hG.trans (uniform_error hC hR hr)
  have hgc := hg.trans (uniform_error (by positivity : 0 ≤ 4*B) hR hr)
  have hs : 3*(C/R^3) ≤ κ := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (pow_pos hR 3)).mpr hsmall
  have hh := metric_comparison_from_background hκ (by positivity : 0 ≤ C/R^3)
    (by positivity : 0 ≤ 4*B/R^3) hs hGc hgc hbg
  have he : (1-3*(C/R^3)/κ)/(1+3*(4*B/R^3)/κ)=comparisonFactor C B κ R := by
    unfold comparisonFactor
    congr 1 <;> field_simp
    ring
  rwa [he] at hh

lemma quadratic3_radialNormalize (r : ℝ) (g : AmbientMat) (v : Fin 3 → ℝ) :
    quadratic3 (radialNormalize r g) v=quadratic3 g (fun i => radialScale r i*v i) := by
  unfold quadratic3 radialNormalize
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma radialScale_ne_zero {r : ℝ} (hr : r ≠ 0) (i : Fin 3) : radialScale r i ≠ 0 := by
  fin_cases i
  · change Real.sqrt (1+r^2) ≠ 0
    positivity
  · change 1/r ≠ 0
    exact one_div_ne_zero hr
  · change 1/r ≠ 0
    exact one_div_ne_zero hr

lemma radialNormalize_comparison {r c : ℝ} {G g : AmbientMat} (hr : r ≠ 0)
    (h : ∀ v, c*quadratic3 (radialNormalize r g) v ≤ quadratic3 (radialNormalize r G) v) :
    ∀ v, c*quadratic3 g v ≤ quadratic3 G v := by
  intro v
  have hh := h (fun i => v i/radialScale r i)
  rw [quadratic3_radialNormalize,quadratic3_radialNormalize] at hh
  have he : (fun i => radialScale r i*(v i/radialScale r i))=v := by
    funext i
    field_simp [radialScale_ne_zero hr i]
  rwa [he] at hh

end
end CKSAngularGeometry

end

end OAI
