import OAI.Analysis.HenonEmden.SpatialPressure

namespace OAI

universe uE uE2 uE3 uE4

section PairPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open LineCoordinates

def directionalFactor {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : sphere (0:E) 1) (z : E × E) : ℝ :=
  (inner ℝ (e:E) (z.1-z.2))^2/‖z.1-z.2‖^2

@[fun_prop] lemma measurable_directionalFactor {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (e : sphere (0:E) 1) : Measurable (directionalFactor e) := by
  unfold directionalFactor; fun_prop
lemma directionalFactor_bounds {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : sphere (0:E) 1) (z : E × E) : 0 ≤ directionalFactor e z ∧ directionalFactor e z ≤ 1 := by
  have hh : |inner ℝ (e:E) (z.1-z.2)| ≤ ‖z.1-z.2‖ := by
    simpa only [norm_unit,one_mul] using abs_real_inner_le_norm (e:E) (z.1-z.2)
  refine ⟨by unfold directionalFactor; positivity,?_⟩
  unfold directionalFactor
  by_cases hz : z.1-z.2=0
  · simp [hz]
  · apply (div_le_one (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hh

lemma coordinate_kernel {n : ℕ} (e : sphere (0:Space n) 1) (z z' : transverse e × ℝ) :
    LayerPressure.splitKernel n (newtonDenom n)⁻¹ (z,z') =
      newtonKernel n (measurableEquiv e z,measurableEquiv e z') := by
  unfold LayerPressure.splitKernel IntervalGeometry.kernel newtonKernel
  rw [← distance_sq,dist_eq_norm,← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
  congr 2
  ring

lemma coordinate_direction {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (e : sphere (0:E) 1) (z z' : transverse e × ℝ) :
    LayerPressure.splitDirection (z,z') = directionalFactor e (measurableEquiv e z,measurableEquiv e z') := by
  have hi : inner ℝ (e:E) (measurableEquiv e z-measurableEquiv e z') = z.2-z'.2 := by
    simp only [measurableEquiv_apply,inner_sub_right,inner_add_right,inner_smul_right,
      inner_transverse,real_inner_self_eq_norm_sq,norm_unit,one_pow,mul_one,zero_add]
  unfold LayerPressure.splitDirection directionalFactor
  rw [hi,← distance_sq,dist_eq_norm]

namespace SpatialComponents
open Cutoff AdaptiveCap LineComponents LayerTonelli

def spatialPairLeft {n : ℕ} (f g : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1)
    (z : (Space n × ℝ) × (Space n × ℝ)) : ℝ :=
  (lineWeight volume f κ δ (e,z.1)+lineWeight volume g κ δ (e,z.2))*newtonKernel n (z.1.1,z.2.1)

def spatialPairRight {n : ℕ} (f g : Space n → ℝ) (κ δ : ℝ) (e : sphere (0:Space n) 1)
    (z : (Space n × ℝ) × (Space n × ℝ)) : ℝ :=
  lineWeight volume f κ δ (e,z.1)*
    ((newtonKernel n (lowerPoint f (e,z.1),z.2.1)+newtonKernel n (upperPoint f (e,z.1),z.2.1))/2)+
  lineWeight volume g κ δ (e,z.2)*
    ((newtonKernel n (z.1.1,lowerPoint g (e,z.2))+newtonKernel n (z.1.1,upperPoint g (e,z.2)))/2)+
  (((n:ℝ)-2)*weight volume κ e z.1.1*directionalFactor e (z.1.1,z.2.1)+
    |lineWeight volume f κ δ (e,z.1)-lineWeight volume g κ δ (e,z.2)|)*newtonKernel n (z.1.1,z.2.1)

lemma measurable_spatialPairLeft {n : ℕ} (hn : 1 ≤ n) {f g : Space n → ℝ}
    (hf : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hg : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < g z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:Space n) 1) :
    Measurable (spatialPairLeft f g κ δ e) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm1 := measurable_lineWeight volume hf hκ hκ1 δ
  have hm2 := measurable_lineWeight volume hg hκ hκ1 δ
  unfold spatialPairLeft
  fun_prop

lemma measurable_spatialPairRight {n : ℕ} (hn : 1 ≤ n) {f g : Space n → ℝ}
    (hf : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hg : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < g z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:Space n) 1) :
    Measurable (spatialPairRight f g κ δ e) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm1 := measurable_lineWeight volume hf hκ hκ1 δ
  have hm2 := measurable_lineWeight volume hg hκ hκ1 δ
  have hlo1 := measurable_lowerPoint hf
  have hlo2 := measurable_lowerPoint hg
  have hhi1 := measurable_upperPoint hf
  have hhi2 := measurable_upperPoint hg
  have hh := (continuous_weight volume hκ hκ1 e).measurable
  unfold spatialPairRight
  fun_prop

lemma spatial_global_nonnegative_pressure {n : ℕ} (hn : 3 ≤ n) {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1})
    (hgo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < g z.1})
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (δ : ℝ) (e : sphere (0:Space n) 1) :
    (∫⁻ z, ENNReal.ofReal (spatialPairLeft f g κ δ e z)
      ∂(layerMeasure volume f).prod (layerMeasure volume g)) ≤
    ∫⁻ z, ENNReal.ofReal (spatialPairRight f g κ δ e z)
      ∂(layerMeasure volume f).prod (layerMeasure volume g) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have : Nontrivial (transverse e) := transverse_nontrivial (by simp; omega) e
  have hp := LayerPressure.global_nonnegative_pressure (volume : Measure (transverse e)) n hn
    (inv_nonneg.mpr (newtonDenom_pos hn).le) (hf.comp (measurableEquiv e).measurable)
    (hg.comp (measurableEquiv e).measurable) (coordinate_layer_open e hfo) (coordinate_layer_open e hgo)
    ((continuous_weight volume hκ hκ1 e).comp (continuous_measurableEquiv e))
    (continuous_d.comp (continuous_measurableEquiv e))
    (fun x => weight_nonneg volume κ e (measurableEquiv e x)) δ
  have hmp := (measurePreserving_coordinateLayer e hf).prod (measurePreserving_coordinateLayer e hg)
  rw [← hmp.lintegral_comp (measurable_spatialPairLeft (by omega) hfo hgo hκ hκ1 δ e).ennreal_ofReal,
    ← hmp.lintegral_comp (measurable_spatialPairRight (by omega) hfo hgo hκ hκ1 δ e).ennreal_ofReal]
  convert hp using 1
  · apply lintegral_congr
    intro z
    congr 1
    simp only [LayerPressure.pairLeft,spatialPairLeft,coordinate_sourceWeight e hfo hκ hκ1,
      coordinate_sourceWeight e hgo hκ hκ1,coordinate_kernel]
    rfl
  · apply lintegral_congr
    intro z
    congr 1
    simp only [LayerPressure.pairRight,spatialPairRight,coordinate_sourceWeight e hfo hκ hκ1,
      coordinate_sourceWeight e hgo hκ hκ1,coordinate_kernel,coordinate_direction,
      coordinate_sourceLower,coordinate_sourceUpper,Function.comp_apply]
    rfl

end SpatialComponents
end HenonLaneEmden
end
end PairPressure

end OAI
