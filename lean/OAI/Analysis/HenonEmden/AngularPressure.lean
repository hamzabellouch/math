import OAI.Analysis.HenonEmden.DirectionalPressure

namespace OAI

section AngularPressure

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap LayerTonelli

lemma integrable_cap_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (x : Space n) :
    Integrable (fun e : sphere (0:Space n) 1 => weight volume κ e x) volume.toSphere := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  exact (integrable_const (boundConstant volume κ)).mono' (continuous_weight_direction volume κ x).aestronglyMeasurable
    (ae_of_all _ (fun e => by rw [Real.norm_eq_abs,abs_of_nonneg (weight_nonneg volume _ _ _)]; exact weight_le_constant volume hκ hκ1 e x))

lemma lintegral_cap_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (x : Space n) :
    (∫⁻ e : sphere (0:Space n) 1, ENNReal.ofReal (weight volume κ e x) ∂volume.toSphere) =
      ENNReal.ofReal (w n x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cap_weight hn hκ hκ1 x)
    (ae_of_all _ (fun e => weight_nonneg volume κ e x)),integral_weight volume hκ hκ1]
  simp only [finrank_euclideanSpace_fin]

lemma lintegral_angular_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {F : Space n → ℝ} (hF : Measurable F) :
    (∫⁻ e : sphere (0:Space n) 1, ∫⁻ x, ENNReal.ofReal (weight volume κ e x)*ENNReal.ofReal (F x) ∂volume
      ∂volume.toSphere) = ∫⁻ x, ENNReal.ofReal (w n x)*ENNReal.ofReal (F x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hM := (measurable_weight volume hκ hκ1).ennreal_ofReal.mul (hF.comp measurable_snd).ennreal_ofReal
  rw [lintegral_lintegral_swap hM.aemeasurable]
  apply lintegral_congr
  intro x
  rw [lintegral_mul_const _ (continuous_weight_direction volume κ x).measurable.ennreal_ofReal,
    lintegral_cap_weight hn hκ hκ1]

lemma lintegral_angular_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    (∫⁻ e : sphere (0:Space n) 1, weightedEnergyN (weight volume κ e) u q B ∂volume.toSphere) =
      weightedEnergyN (w n) u q B := by
  unfold weightedEnergyN
  simp_rw [mul_assoc,ENNReal.ofReal_mul (weight_nonneg volume κ _ _)]
  simp_rw [ENNReal.ofReal_mul (w_nonneg n _)]
  exact lintegral_angular_weight hn hκ hκ1 ((measurable_source hu q B).mul hu.measurable)

namespace SpatialComponents
lemma lintegral_angular_loss {n : ℕ} (hn : 1 ≤ n) {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {f u : Space n → ℝ} (_hf : Measurable f) (hu : Measurable u) (hun : ∀ x, 0 ≤ u x)
    (hfo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    (∫⁻ e : sphere (0:Space n) 1, lossIntegral u f κ δ e ∂volume.toSphere) =
      ∫⁻ z, ENNReal.ofReal (u z.1*averagedLoss volume f κ δ z) ∂layerMeasure volume f := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hM : Measurable (fun z : sphere (0:Space n) 1 × (Space n × ℝ) =>
      ENNReal.ofReal ((weight volume κ z.1 z.2.1-lineWeight volume f κ δ z)*u z.2.1)) := by
    exact ((((measurable_weight volume hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)).sub
      (measurable_lineWeight volume hfo hκ hκ1 δ)).mul (hu.comp measurable_snd.fst)).ennreal_ofReal
  unfold lossIntegral
  rw [lintegral_lintegral_swap hM.aemeasurable]
  apply lintegral_congr
  intro z
  have hi := (integrable_loss volume hfo hκ hκ1 δ z.1 z.2).mul_const (u z.1)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun e => mul_nonneg (sub_nonneg.mpr (lineWeight_le volume f κ δ (e,z))) (hun z.1))),
    integral_mul_const]
  congr 1
  exact mul_comm _ _
end SpatialComponents
end HenonLaneEmden
end
end AngularPressure

end OAI
