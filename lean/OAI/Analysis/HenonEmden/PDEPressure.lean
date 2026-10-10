import OAI.Analysis.HenonEmden.GlobalLoss

namespace OAI

section PDEPressure

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open LayerTonelli

lemma lintegral_pair_interaction {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ z, F (z.1.1,z.2.1)*ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))
       ∂(layerMeasure volume f).prod (layerMeasure volume g)) = ∫⁻ z, F z ∂interaction f g := by
  rw [lintegral_pair_spatial volume hf hg (F := fun z => F z*ENNReal.ofReal (newtonKernel n z)) (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),
    lintegral_interaction hf hg hF]
  apply lintegral_congr
  intro z
  ring

namespace SpatialComponents
open Cutoff AdaptiveCap LayerPressure

lemma IsSolution_pairRight_recovery {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    (∫⁻ z, ENNReal.ofReal (spatialPairRight (source u q B) (source v p A) κ δ e z)
      ∂(layerMeasure volume (source u q B)).prod (layerMeasure volume (source v p A))) =
      (endpointIntegral u (source u q B) κ δ e+endpointIntegral v (source v p A) κ δ e)+
      capPressureIntegral (source u q B) (source v p A) κ e+
      pairMismatchIntegral (source u q B) (source v p A) κ δ e := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := isOpen_source_subgraph h.regular_u h.positive_u q B
  have hg := isOpen_source_subgraph h.regular_v h.positive_v p A
  have hfM := measurable_source h.continuous_u q B
  have hgM := measurable_source h.continuous_v p A
  have hm1 : Measurable (fun z : Space n × ℝ => lineWeight volume (source u q B) κ δ (e,z)) :=
    (measurable_lineWeight volume hf hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hm2 : Measurable (fun z : Space n × ℝ => lineWeight volume (source v p A) κ δ (e,z)) :=
    (measurable_lineWeight volume hg hκ hκ1 δ).comp (measurable_const.prodMk measurable_id)
  have hlo1 : Measurable (fun z : Space n × ℝ => lowerPoint (source u q B) (e,z)) :=
    (measurable_lowerPoint hf).comp (measurable_const.prodMk measurable_id)
  have hhi1 : Measurable (fun z : Space n × ℝ => upperPoint (source u q B) (e,z)) :=
    (measurable_upperPoint hf).comp (measurable_const.prodMk measurable_id)
  have hlo2 : Measurable (fun z : Space n × ℝ => lowerPoint (source v p A) (e,z)) :=
    (measurable_lowerPoint hg).comp (measurable_const.prodMk measurable_id)
  have hhi2 : Measurable (fun z : Space n × ℝ => upperPoint (source v p A) (e,z)) :=
    (measurable_upperPoint hg).comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (weight volume κ e : Space n → ℝ) := (continuous_weight volume hκ hκ1 e).measurable
  have hn2 : 0 ≤ (n:ℝ)-2 := by exact_mod_cast (show (2:ℝ) ≤ n by exact_mod_cast (show 2 ≤ n by omega)) |> sub_nonneg.mpr
  have he (z : (Space n × ℝ) × (Space n × ℝ)) :
      ENNReal.ofReal (spatialPairRight (source u q B) (source v p A) κ δ e z) =
        ENNReal.ofReal (lineWeight volume (source u q B) κ δ (e,z.1))*
          ((ENNReal.ofReal (newtonKernel n (lowerPoint (source u q B) (e,z.1),z.2.1))+
            ENNReal.ofReal (newtonKernel n (upperPoint (source u q B) (e,z.1),z.2.1)))/2)+
        ENNReal.ofReal (lineWeight volume (source v p A) κ δ (e,z.2))*
          ((ENNReal.ofReal (newtonKernel n (z.1.1,lowerPoint (source v p A) (e,z.2)))+
            ENNReal.ofReal (newtonKernel n (z.1.1,upperPoint (source v p A) (e,z.2))))/2)+
        ENNReal.ofReal (((n:ℝ)-2)*weight volume κ e z.1.1*directionalFactor e (z.1.1,z.2.1))*
          ENNReal.ofReal (newtonKernel n (z.1.1,z.2.1))+
        ENNReal.ofReal (|lineWeight volume (source u q B) κ δ (e,z.1)-lineWeight volume (source v p A) κ δ (e,z.2)| *
          newtonKernel n (z.1.1,z.2.1)) := by
    have hk := newtonKernel_nonneg hn
    have hχ := lineWeight_nonneg (μ := (volume : Measure (Space n)))
    have hh0 := weight_nonneg (μ := (volume : Measure (Space n)))
    have hd := (directionalFactor_bounds e (z.1.1,z.2.1)).1
    have hχ1 := hχ (source u q B) κ δ (e,z.1)
    have hχ2 := hχ (source v p A) κ δ (e,z.2)
    have hh1 := hh0 κ e z.1.1
    have hk0 := hk (z.1.1,z.2.1)
    have hk1 := hk (lowerPoint (source u q B) (e,z.1),z.2.1)
    have hk2 := hk (upperPoint (source u q B) (e,z.1),z.2.1)
    have hk3 := hk (z.1.1,lowerPoint (source v p A) (e,z.2))
    have hk4 := hk (z.1.1,upperPoint (source v p A) (e,z.2))
    unfold spatialPairRight
    rw [add_mul]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    rw [ENNReal.ofReal_mul (hχ _ _ _ _),ENNReal.ofReal_mul (hχ _ _ _ _),
      ENNReal.ofReal_div_of_pos (show (0:ℝ)<2 by norm_num),
      ENNReal.ofReal_div_of_pos (show (0:ℝ)<2 by norm_num),
      ENNReal.ofReal_add (hk _) (hk _),ENNReal.ofReal_add (hk _) (hk _),
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hn2 (hh0 _ _ _)) hd),ENNReal.ofReal_ofNat]
    ring
  have hm1' := measurable_lineWeight volume hf hκ hκ1 δ
  have hm2' := measurable_lineWeight volume hg hκ hκ1 δ
  have hlo1' := measurable_lowerPoint hf
  have hhi1' := measurable_upperPoint hf
  have hlo2' := measurable_lowerPoint hg
  have hhi2' := measurable_upperPoint hg
  have hh' := measurable_weight (volume : Measure (Space n)) hκ hκ1
  simp_rw [he]
  rw [lintegral_add_left (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),lintegral_add_left (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),lintegral_add_left (by fun_prop [measurable_newtonKernel,measurable_directionalFactor]),
    lintegral_pair_endpoint_average volume hgM (measurable_newtonKernel n).ennreal_ofReal hm1.ennreal_ofReal hlo1 hhi1,
    lintegral_pair_endpoint_average_right volume hfM (measurable_newtonKernel n).ennreal_ofReal
      (fun x y => congrArg ENNReal.ofReal (newtonKernel_symm n x y)) hm2.ennreal_ofReal hlo2 hhi2,
    lintegral_pair_interaction hfM hgM (F := fun z => ENNReal.ofReal (((n:ℝ)-2)*weight volume κ e z.1*directionalFactor e z)) (by fun_prop [measurable_newtonKernel,measurable_directionalFactor])]
  simp_rw [weighted_potential_endpoint (by omega) h hq hκ hκ1 hδ e,
    weighted_potential_endpoint (by omega) h.swap hp hκ hκ1 hδ e]
  rfl

lemma IsSolution_pressure_comparison {n : ℕ} (hn : 3 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 ≤ δ) (e : sphere (0:Space n) 1) :
    positionIntegral u (source u q B) κ δ e+positionIntegral v (source v p A) κ δ e ≤
      (endpointIntegral u (source u q B) κ δ e+endpointIntegral v (source v p A) κ δ e)+
      capPressureIntegral (source u q B) (source v p A) κ e+
      pairMismatchIntegral (source u q B) (source v p A) κ δ e := by
  rw [← IsSolution_pairLeft_recovery (by omega) h hp hq hκ hκ1,
    ← IsSolution_pairRight_recovery hn h hp hq hκ hκ1 hδ]
  exact spatial_global_nonnegative_pressure hn (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) (isOpen_source_subgraph h.regular_u h.positive_u q B)
    (isOpen_source_subgraph h.regular_v h.positive_v p A) hκ hκ1 δ e

end SpatialComponents
end HenonLaneEmden
end
end PDEPressure

end OAI
