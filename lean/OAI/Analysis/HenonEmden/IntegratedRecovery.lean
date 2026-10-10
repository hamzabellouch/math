import OAI.Analysis.HenonEmden.WeightedEnergy

namespace OAI

section IntegratedRecovery

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden.SpatialComponents
open Cutoff AdaptiveCap LayerTonelli

lemma lintegral_weight_layer {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (hf : Measurable (source u q B))
    {χ : Space n → ℝ} (hχ : Measurable χ) (_hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.1*u z.1) ∂layerMeasure volume (source u q B)) =
      weightedEnergyN χ u q B := by
  rw [lintegral_layerMeasure_fst volume hf (F := fun x => ENNReal.ofReal (χ x*u x)) (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (source_nonneg hu0 q B x)]
  congr 1
  ring

lemma lintegral_pressure_root {n : ℕ} {u : Space n → ℝ} {q B : ℝ}
    (hu : Measurable u) (hup : ∀ x, 0 < u x) (hq : 0 < q) (hf : Measurable (source u q B))
    {χ : Space n → ℝ} (hχ : Measurable χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.1*(u z.1-sourceRoot q B z)) ∂layerMeasure volume (source u q B)) =
      ENNReal.ofReal (1/(q+1))*weightedEnergyN χ u q B := by
  rw [lintegral_layerMeasure volume hf (by fun_prop)]
  simp_rw [ENNReal.ofReal_mul (hχ0 _)]
  have he (x : Space n) : (∫⁻ t in Ioo 0 (source u q B x), ENNReal.ofReal (χ x)*
      ENNReal.ofReal (u x-sourceRoot q B (x,t))) =
      ENNReal.ofReal (1/(q+1))*ENNReal.ofReal (χ x*source u q B x*u x) := by
    rw [lintegral_const_mul _ (by fun_prop),lintegral_source_residual hup hq,
      ← ENNReal.ofReal_mul (hχ0 x),← ENNReal.ofReal_mul (one_div_nonneg.mpr (by linarith : 0 ≤ q+1))]
    congr 1
    ring
  simp_rw [he]
  exact lintegral_const_mul _ (by fun_prop)

lemma IsSolution_endpointIntegral_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    endpointIntegral u (source u q B) κ δ e ≤
      ENNReal.ofReal (1+endpointConstant q B*δ)*weightedEnergyN (weight volume κ e) u q B := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have huM := h.continuous_u.measurable
  have hfM := measurable_source h.continuous_u q B
  have hm := (continuous_weight volume hκ hκ1 e).measurable
  have hd : Measurable (d : Space n → ℝ) := continuous_d.measurable
  have hc := endpointConstant_nonneg q B
  have hpoint (z : Space n × ℝ) (hz : z ∈ sourceSubgraph (source u q B)) :
      lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z) ≤
      (1+endpointConstant q B*δ)*(weight volume κ e z.1*u z.1) := by
    have hχ := lineWeight_nonneg volume (source u q B) κ δ (e,z)
    have hh := weight_nonneg volume κ e z.1
    have hu0 := (h.positive_u z.1).le
    by_cases hpos : 0 < lineWeight volume (source u q B) κ δ (e,z)
    · have he := (abs_le.mp (source_endpoint_error (by omega) h.regular_u h.positive_u hq hκ hκ1 hδ hpos)).2
      have hr := (sourceRoot_bounds h.positive_u hq hz).2
      change sourceRoot q B z ≤ u z.1 at hr
      have hε : endpointConstant q B*δ*d z.1*u z.1 ≤ endpointConstant q B*δ*u z.1 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (d_le_one z.1) (mul_nonneg hc hδ)) hu0 |>.trans_eq (by ring)
      have hle : endpointAverage u (source u q B) (e,z) ≤ (1+endpointConstant q B*δ)*u z.1 := by
        change endpointAverage u (source u q B) (e,z)-sourceRoot q B z ≤ _ at he
        nlinarith
      calc
        _ ≤ lineWeight volume (source u q B) κ δ (e,z)*((1+endpointConstant q B*δ)*u z.1) :=
          mul_le_mul_of_nonneg_left hle hχ
        _ ≤ weight volume κ e z.1*((1+endpointConstant q B*δ)*u z.1) :=
          mul_le_mul_of_nonneg_right (lineWeight_le volume _ _ _ _) (by positivity)
        _ = _ := by ring
    · rw [le_antisymm (not_lt.mp hpos) hχ,zero_mul]
      positivity
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((1+endpointConstant q B*δ)*(weight volume κ e z.1*u z.1))
        ∂layerMeasure volume (source u q B) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_sourceSubgraph hfM)] with z hz
      exact ENNReal.ofReal_le_ofReal (hpoint z hz)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (show 0 ≤ 1+endpointConstant q B*δ by positivity)]
      rw [lintegral_const_mul _ (by fun_prop),lintegral_weight_layer h.continuous_u.measurable
        (fun x => (h.positive_u x).le) hfM hm (weight_nonneg volume κ e)]

lemma IsSolution_endpointIntegral_finite {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    endpointIntegral u (source u q B) κ δ e ≠ ⊤ := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (h.weightedEnergyN_finite hn (continuous_weight volume hκ hκ1 e) (compactSupport_weight κ e)))
    (IsSolution_endpointIntegral_bound hn h hq hκ hκ1 hδ e)

lemma IsSolution_integrated_pressure_recovery {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    ENNReal.ofReal (1/(q+1))*weightedEnergyN (weight volume κ e) u q B+
      endpointIntegral u (source u q B) κ δ e ≤
      positionIntegral u (source u q B) κ δ e+lossIntegral u (source u q B) κ δ e+
      ENNReal.ofReal (endpointConstant q B*δ)*weightedEnergyN (fun x => d x*weight volume κ e x) u q B := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have huM := h.continuous_u.measurable
  have hfM := measurable_source h.continuous_u q B
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hm := (continuous_weight volume hκ hκ1 e).measurable
  have hmχ : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hlo := measurable_lowerPoint hf
  have hhi := measurable_upperPoint hf
  have hd : Measurable (d : Space n → ℝ) := continuous_d.measurable
  have hc := endpointConstant_nonneg q B
  have hrec := lintegral_mono_ae (μ := layerMeasure volume (source u q B)) (show ∀ᵐ z ∂layerMeasure volume (source u q B),
      ENNReal.ofReal (weight volume κ e z.1*(u z.1-sourceRoot q B z))+
        ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*endpointAverage u (source u q B) (e,z)) ≤
      ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z)*u z.1)+
        ENNReal.ofReal ((weight volume κ e z.1-lineWeight volume (source u q B) κ δ (e,z))*u z.1)+
        ENNReal.ofReal (endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1) from by
    filter_upwards [ae_restrict_mem (measurableSet_sourceSubgraph hfM)] with z hz
    exact source_pressure_recovery_pointwise (by omega) h.regular_u h.positive_u hq hκ hκ1 hδ e hz)
  rw [lintegral_add_left (by fun_prop),lintegral_add_left (by fun_prop),lintegral_add_left (by fun_prop),
    lintegral_pressure_root huM h.positive_u hq hfM hm (weight_nonneg volume κ e)] at hrec
  change _ ≤ positionIntegral u (source u q B) κ δ e+lossIntegral u (source u q B) κ δ e+_ at hrec
  convert hrec using 1
  congr 1
  have he (z : Space n × ℝ) : ENNReal.ofReal (endpointConstant q B*δ*d z.1*weight volume κ e z.1*u z.1) =
      ENNReal.ofReal (endpointConstant q B*δ)*ENNReal.ofReal ((d z.1*weight volume κ e z.1)*u z.1) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hc hδ)]; congr 1; ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop),
    lintegral_weight_layer huM (fun x => (h.positive_u x).le) hfM (by fun_prop)
      (fun x => mul_nonneg (d_nonneg x) (weight_nonneg volume κ e x))]

end HenonLaneEmden.SpatialComponents
end
end IntegratedRecovery

end OAI
