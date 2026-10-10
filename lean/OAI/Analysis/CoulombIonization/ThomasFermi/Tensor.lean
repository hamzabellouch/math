import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.Lp

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace CoulombAnalysis
section Tensor
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite ν]

lemma tf_memLp_prod {f : α → ℝ} {g : β → ℝ} (hf : MemLp f (5 / 3) μ)
    (hg : MemLp g (5 / 3) ν) : MemLp (fun p : α × β => f p.1 * g p.2) (5 / 3) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) :=
    hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd
  apply (integrable_norm_rpow_iff hm
    (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp
  have hi := (hf.integrable_norm_rpow (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))).mul_prod
    (hg.integrable_norm_rpow (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num)))
  simpa only [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] using hi

def tfTensor (f : TFLp μ) (g : TFLp ν) : TFLp (μ.prod ν) :=
  (tf_memLp_prod (Lp.memLp f) (Lp.memLp g)).toLp (fun p => f p.1 * g p.2)

lemma tfTensor_coe (f : TFLp μ) (g : TFLp ν) :
    tfTensor f g =ᵐ[μ.prod ν] fun p => f p.1 * g p.2 := MemLp.coeFn_toLp _

variable [SFinite μ]

lemma tfTensor_norm (f : TFLp μ) (g : TFLp ν) : ‖tfTensor f g‖ = ‖f‖ * ‖g‖ := by
  apply (Real.rpow_left_inj (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by norm_num : (5 / 3 : ℝ) ≠ 0)).mp
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), tfLp_norm_rpow, tfLp_norm_rpow, tfLp_norm_rpow]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [tfTensor_coe f g] with p hp
  rw [hp, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

omit [SFinite μ] in
lemma tfTensor_add_left (f₁ f₂ : TFLp μ) (g : TFLp ν) :
    tfTensor (f₁ + f₂) g = tfTensor f₁ g + tfTensor f₂ g := by
  apply Lp.ext
  filter_upwards [tfTensor_coe (f₁ + f₂) g, tfTensor_coe f₁ g, tfTensor_coe f₂ g,
    Lp.coeFn_add (tfTensor f₁ g) (tfTensor f₂ g),
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_add f₁ f₂)] with p hp h1 h2 he ha
  simp only [hp, he, Pi.add_apply, h1, h2, ha, add_mul]

omit [SFinite μ] in
lemma tfTensor_add_right (f : TFLp μ) (g₁ g₂ : TFLp ν) :
    tfTensor f (g₁ + g₂) = tfTensor f g₁ + tfTensor f g₂ := by
  apply Lp.ext
  filter_upwards [tfTensor_coe f (g₁ + g₂), tfTensor_coe f g₁, tfTensor_coe f g₂,
    Lp.coeFn_add (tfTensor f g₁) (tfTensor f g₂),
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_add g₁ g₂)] with p hp h1 h2 he ha
  simp only [hp, he, Pi.add_apply, h1, h2, ha, mul_add]

omit [SFinite μ] in
lemma tfTensor_smul_left (c : ℝ) (f : TFLp μ) (g : TFLp ν) :
    tfTensor (c • f) g = c • tfTensor f g := by
  apply Lp.ext
  filter_upwards [tfTensor_coe (c • f) g, tfTensor_coe f g,
    Lp.coeFn_smul c (tfTensor f g), (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c f)]
    with p hp he hs hc
  simp only [hp, hs, Pi.smul_apply, smul_eq_mul, he, hc, mul_assoc]

omit [SFinite μ] in
lemma tfTensor_smul_right (c : ℝ) (f : TFLp μ) (g : TFLp ν) :
    tfTensor f (c • g) = c • tfTensor f g := by
  apply Lp.ext
  filter_upwards [tfTensor_coe f (c • g), tfTensor_coe f g,
    Lp.coeFn_smul c (tfTensor f g), (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c g)]
    with p hp he hs hc
  simp only [hp, hs, Pi.smul_apply, smul_eq_mul, he, hc]
  ring

def tfTensorₗ : TFLp μ →ₗ[ℝ] TFLp ν →ₗ[ℝ] TFLp (μ.prod ν) :=
  LinearMap.mk₂ ℝ tfTensor tfTensor_add_left tfTensor_smul_left
    tfTensor_add_right tfTensor_smul_right

lemma tfTensorₗ_bound (f : TFLp μ) (g : TFLp ν) :
    ‖tfTensorₗ f g‖ ≤ 1 * ‖f‖ * ‖g‖ := by
  change ‖tfTensor f g‖ ≤ _
  rw [tfTensor_norm, one_mul]

def tfTensorL : TFLp μ →L[ℝ] TFLp ν →L[ℝ] TFLp (μ.prod ν) :=
  tfTensorₗ.mkContinuous₂ 1 tfTensorₗ_bound

lemma tfTensorL_apply (f : TFLp μ) (g : TFLp ν) : tfTensorL f g = tfTensor f g := rfl

end Tensor

instance tfDualFact : Fact ((1 : ENNReal) ≤ 5 / 2) :=
  ⟨(ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by norm_num)⟩
instance tfConjugate : ENNReal.HolderConjugate (5 / 2) (5 / 3) := by
  rw [ENNReal.holderConjugate_iff,
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← ENNReal.add_div]
  norm_num [ENNReal.div_self]

end CoulombAnalysis

end

end OAI
