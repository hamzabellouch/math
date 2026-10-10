import OAI.Analysis.HenonEmden.PairRecovery

namespace OAI

section RootRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.WeightedLayers

lemma weighted_layer_identity_ennreal {w u q : ℝ} (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) :
    (∫⁻ t in Ioo 0 (w*u^q), ENNReal.ofReal (u-(t/w)^(1/q))) =
      ENNReal.ofReal ((w*u^q*u)/(q+1)) := by
  have hf : 0 < w*u^q := mul_pos hw (Real.rpow_pos_of_pos hu _)
  have hc : Continuous (fun t : ℝ => u-(t/w)^(1/q)) := by
    apply continuous_const.sub
    exact (continuous_id.div_const w).rpow_const (fun _ => Or.inr (one_div_nonneg.mpr hq.le))
  have hi : IntegrableOn (fun t : ℝ => u-(t/w)^(1/q)) (Ioo 0 (w*u^q)) :=
    (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hf.le,
      weighted_layer_identity hw hu hq,Real.rpow_add hu,Real.rpow_one,mul_assoc]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sub_nonneg.mpr (layer_root_bounds hw hu hq ht.1.le ht.2.le).2

end HenonLaneEmden.WeightedLayers
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap WeightedLayers LayerTonelli

def sourceRoot {n : ℕ} (q B : ℝ) (z : Space n × ℝ) : ℝ := (z.2/‖z.1‖^B)^(1/q)
@[fun_prop] lemma measurable_sourceRoot (n : ℕ) (q B : ℝ) : Measurable (sourceRoot (n:=n) q B) := by
  unfold sourceRoot; fun_prop

lemma sourceRoot_bounds {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : ∀ x, 0 < u x) (hq : 0 < q) {z : Space n × ℝ}
    (hz : 0 < z.2 ∧ z.2 < source u q B z.1) :
    0 ≤ sourceRoot q B z ∧ sourceRoot q B z ≤ u z.1 := by
  have hx : z.1 ≠ 0 := by
    intro hx; rw [hx,source_zero] at hz; linarith [hz.1,hz.2]
  exact layer_root_bounds (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) B) (hu _) hq hz.1.le
    (by rw [← source_off_zero _ _ _ hx]; exact hz.2.le)

lemma lintegral_source_residual {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : ∀ x, 0 < u x) (hq : 0 < q) (x : Space n) :
    (∫⁻ t in Ioo 0 (source u q B x), ENNReal.ofReal (u x-sourceRoot q B (x,t))) =
      ENNReal.ofReal (source u q B x*u x/(q+1)) := by
  by_cases hx : x=0
  · simp [hx,source_zero]
  · rw [source_off_zero _ _ _ hx]
    exact weighted_layer_identity_ennreal (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) B) (hu _) hq

lemma source_pressure_recovery_pointwise {n : ℕ} (hn : 1 ≤ n) {u : Space n → ℝ} {q B κ δ : ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (hq : 0 < q) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ)
    (e : sphere (0:Space n) 1) {z : Space n × ℝ}
    (hz : 0 < z.2 ∧ z.2 < source u q B z.1) :
    ENNReal.ofReal (weight volume κ e z.1*(u z.1-sourceRoot q B z))+
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z)) ≤
    ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*u z.1)+
      ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*u z.1)+
      ENNReal.ofReal (endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1) := by
  have hnχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
  have hleh := lineWeight_le volume (source u q B) κ δ (e,z)
  have hh := weight_nonneg volume κ e z.1
  have hu0 : 0 ≤ u z.1 := (hup _).le
  have he : 0 ≤ endpointAverage u (source u q B) (e,z) := by
    exact div_nonneg (add_nonneg (hup _).le (hup _).le) (by norm_num)
  have hr := sourceRoot_bounds hup hq hz
  rw [← ENNReal.ofReal_add (mul_nonneg hh (sub_nonneg.mpr hr.2)) (mul_nonneg hnχ he),
    ← ENNReal.ofReal_add (mul_nonneg hnχ (hup _).le) (mul_nonneg (sub_nonneg.mpr hleh) (hup _).le),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hnχ (hup _).le) (mul_nonneg (sub_nonneg.mpr hleh) (hup _).le))
      (by have hc := endpointConstant_nonneg q B; have hd := d_nonneg z.1; positivity)]
  apply ENNReal.ofReal_le_ofReal
  by_cases hχ : 0 < lineWeight volume (source u q B) κ δ (e,z)
  · have hs := source_endpoint_error hn hu hup hq hκ hκ1 hδ hχ
    have hp := pressure_recovery_pointwise hnχ hleh hr.1 hs
    change _ ≤ _ at hp
    dsimp only [sourceRoot] at *
    nlinarith
  · have hzero := le_antisymm (not_lt.mp hχ) hnχ
    rw [hzero]
    have hc := endpointConstant_nonneg q B
    have hd := d_nonneg z.1
    have htail : 0 ≤ endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1 := by positivity
    nlinarith [mul_nonneg hh hr.1]

end HenonLaneEmden.SpatialComponents
end
end RootRecovery

end OAI
