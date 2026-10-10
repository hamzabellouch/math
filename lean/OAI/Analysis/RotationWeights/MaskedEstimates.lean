import OAI.Analysis.RotationWeights.LaurentCoefficients

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uΩ uX uι uY

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

theorem endpoint_mask_integral_le {Ω : Type uΩ} {X : Type uX} [MeasurableSpace Ω]
    [MeasurableSpace X] (μ : Measure Ω) (x : Ω → X) (hx : Measurable x)
    (H : Set Ω) (hH : MeasurableSet H) (δ : ℝ≥0∞)
    (hdom : Measure.map x (μ.restrict H) ≤ δ • Measure.map x μ)
    (a : X → ℝ≥0∞) (ha : Measurable a) :
    (∫⁻ ω, H.indicator (fun ω => a (x ω)) ω ∂μ) ≤
      δ * ∫⁻ ω, a (x ω) ∂μ := by
  rw [lintegral_indicator hH, ← lintegral_map ha hx]
  calc
    _ ≤ ∫⁻ z, a z ∂δ • Measure.map x μ := lintegral_mono' hdom le_rfl
    _ = _ := by rw [lintegral_smul_measure, lintegral_map ha hx]; rfl

theorem endpoint_masked_squares {Ω : Type uΩ} {X : Type uX} {ι : Type uι} [MeasurableSpace Ω]
    [MeasurableSpace X] [Countable ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (hx : Measurable x)
    (H : ι → Set Ω) (hH : ∀ i, MeasurableSet (H i)) (δ : ℝ≥0∞)
    (hdom : ∀ i, Measure.map x (μ.restrict (H i)) ≤ δ • Measure.map x μ)
    (a : ι → X → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (hsq : ∀ᵐ ω ∂μ, (∑' i, a i (x ω) ^ 2) ≤ 1) :
    (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i (x ω) ^ 2) ω ∂μ) ≤ δ := by
  have hm (i : ι) : Measurable (fun ω => (H i).indicator
      (fun ω => a i (x ω) ^ 2) ω) :=
    (((ha i).comp hx).pow_const 2).indicator (hH i)
  rw [lintegral_tsum (fun i => (hm i).aemeasurable)]
  calc
    _ ≤ ∑' i, δ * ∫⁻ ω, a i (x ω) ^ 2 ∂μ :=
      ENNReal.tsum_le_tsum (fun i => endpoint_mask_integral_le μ x hx (H i) (hH i)
        δ (hdom i) (fun z => a i z ^ 2) ((ha i).pow_const 2))
    _ = δ * ∫⁻ ω, ∑' i, a i (x ω) ^ 2 ∂μ := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact (lintegral_tsum (fun i => show AEMeasurable
        (fun ω => a i (x ω) ^ 2) μ from
          (((ha i).comp hx).pow_const 2).aemeasurable)).symm
    _ ≤ δ * 1 := mul_le_mul' le_rfl (by simpa using lintegral_mono_ae hsq)
    _ = δ := mul_one δ

theorem masked_product_integral_le {Ω : Type uΩ} {ι : Type uι} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure Ω) [SFinite μ]
    (a b : ι → Ω → ℝ≥0∞) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i, Measurable (b i)) (H : ι → Set Ω)
    (hH : ∀ i, MeasurableSet (H i)) (δ : ℝ≥0∞)
    (hfirst : (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i ω ^ 2) ω ∂μ) ≤ δ)
    (hsecond : (∫⁻ ω, ∑' i, b i ω ^ 2 ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i ω * b i ω) ω ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  let A : ι × Ω → ℝ≥0∞ := fun z => (H z.1).indicator (a z.1) z.2
  let B : ι × Ω → ℝ≥0∞ := fun z => b z.1 z.2
  have hA : Measurable A := measurable_from_prod_countable_right
    (fun i => (ha i).indicator (hH i))
  have hB : Measurable B := measurable_from_prod_countable_right hb
  have hApow (z : ι × Ω) : A z ^ (2 : ℝ) =
      (H z.1).indicator (fun ω => a z.1 ω ^ 2) z.2 := by
    rw [ENNReal.rpow_two]
    by_cases hz : z.2 ∈ H z.1 <;> simp [A, hz]
  have hAB (z : ι × Ω) : (A * B) z =
      (H z.1).indicator (fun ω => a z.1 ω * b z.1 ω) z.2 := by
    by_cases hz : z.2 ∈ H z.1 <;> simp [A, B, hz]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count.prod μ)
    (show Real.HolderConjugate 2 2 from by norm_num [Real.holderConjugate_iff])
    hA.aemeasurable hB.aemeasurable
  have hiA : (∫⁻ z, A z ^ (2 : ℝ) ∂Measure.count.prod μ) ≤ δ := by
    rw [lintegral_prod _ (hA.pow_const (2 : ℝ)).aemeasurable, lintegral_count]
    simp_rw [hApow]
    rwa [← lintegral_tsum (fun i => ((ha i).pow_const 2).indicator (hH i) |>.aemeasurable)]
  have hiB : (∫⁻ z, B z ^ (2 : ℝ) ∂Measure.count.prod μ) ≤ 1 := by
    rw [lintegral_prod _ (hB.pow_const (2 : ℝ)).aemeasurable, lintegral_count]
    simpa only [B, ENNReal.rpow_two,
      ← lintegral_tsum (fun i => ((hb i).pow_const 2).aemeasurable)] using hsecond
  have hiAB : (∫⁻ z, (A * B) z ∂Measure.count.prod μ) =
      (∫⁻ ω, ∑' i, (H i).indicator (fun ω => a i ω * b i ω) ω ∂μ) := by
    rw [lintegral_prod _ (hA.mul hB).aemeasurable, lintegral_count]
    simp_rw [hAB]
    exact (lintegral_tsum (fun i => show AEMeasurable
      (fun ω => (H i).indicator (fun ω => a i ω * b i ω) ω) μ from
        (((ha i).mul (hb i)).indicator (hH i)).aemeasurable)).symm
  rw [hiAB] at hcs
  exact hcs.trans (by
    calc
      _ ≤ δ ^ (1 / 2 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hiA (by norm_num))
          (ENNReal.rpow_le_rpow hiB (by norm_num))
      _ = _ := by simp)

theorem retained_sum_enorm_le {ι : Type uι} (z : ι → ℂ) (s : Finset ι)
    (hz : Summable z) (hzero : ∑' i, z i = 0) (a : ι → ℝ≥0∞)
    (ha : ∀ i ∉ s, ‖z i‖ₑ ≤ a i) :
    ‖∑ i ∈ s, z i‖ₑ ≤ ∑' i, a i := by
  classical
  have heq := hz.sum_add_tsum_compl (s := s)
  rw [hzero] at heq
  have hret : (∑ i ∈ s, z i) = -(∑' i : {i // i ∉ s}, z i) :=
    eq_neg_of_add_eq_zero_left heq
  rw [hret, enorm_neg]
  exact enorm_tsum_le_tsum_enorm.trans
    ((ENNReal.tsum_le_tsum (fun i : {i // i ∉ s} => ha i i.property)).trans
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective a))

theorem convolution_cut_bound {ι : Type uι} (z : ι → ℂ) (s : Finset ι)
    (hz : Summable z) (hzero : ∑' i, z i = 0)
    (a b h₁ h₂ : ι → ℝ≥0∞) (r : ℝ≥0∞)
    (hprod : ∑' i, a i * b i ≤ 1)
    (hbound : ∀ i ∉ s, ‖z i‖ₑ ≤ a i * b i * (r + h₁ i + h₂ i)) :
    ‖∑ i ∈ s, z i‖ₑ ≤ r + (∑' i, a i * b i * h₁ i) +
      (∑' i, a i * b i * h₂ i) := by
  apply (retained_sum_enorm_le z s hz hzero _ hbound).trans
  simp_rw [mul_add]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact add_le_add (add_le_add (by simpa only [one_mul] using
      (mul_le_mul' hprod (le_rfl : r ≤ r))) le_rfl) le_rfl

theorem two_endpoint_error_bound {Ω : Type uΩ} {X : Type uX} {Y : Type uY} {ι : Type uι} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → X) (y : Ω → Y) (hx : Measurable x) (hy : Measurable y)
    (a : ι → X → ℝ≥0∞) (b : ι → Y → ℝ≥0∞)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (H₁ H₂ : ι → Set Ω) (hH₁ : ∀ i, MeasurableSet (H₁ i))
    (hH₂ : ∀ i, MeasurableSet (H₂ i)) (δ r : ℝ≥0∞)
    (hdom₁ : ∀ i, Measure.map x (μ.restrict (H₁ i)) ≤ δ • Measure.map x μ)
    (hdom₂ : ∀ i, Measure.map y (μ.restrict (H₂ i)) ≤ δ • Measure.map y μ)
    (hsq₁ : ∀ᵐ ω ∂μ, ∑' i, a i (x ω) ^ 2 ≤ 1)
    (hsq₂ : ∀ᵐ ω ∂μ, ∑' i, b i (y ω) ^ 2 ≤ 1)
    (c : Ω → ℝ≥0∞)
    (hc : ∀ᵐ ω ∂μ, c ω ≤ r +
      (∑' i, (H₁ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω) +
      (∑' i, (H₂ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω)) :
    (∫⁻ ω, c ω ∂μ) ≤ r + δ ^ (1 / 2 : ℝ) + δ ^ (1 / 2 : ℝ) := by
  have hi₁ := endpoint_masked_squares μ x hx H₁ hH₁ δ hdom₁ a ha hsq₁
  have hi₂ := endpoint_masked_squares μ y hy H₂ hH₂ δ hdom₂ b hb hsq₂
  have hbint : (∫⁻ ω, ∑' i, b i (y ω) ^ 2 ∂μ) ≤ 1 := by
    simpa using lintegral_mono_ae hsq₂
  have haint : (∫⁻ ω, ∑' i, a i (x ω) ^ 2 ∂μ) ≤ 1 := by
    simpa using lintegral_mono_ae hsq₁
  have hfirst := masked_product_integral_le μ (fun i ω => a i (x ω))
    (fun i ω => b i (y ω)) (fun i => (ha i).comp hx) (fun i => (hb i).comp hy)
    H₁ hH₁ δ hi₁ hbint
  have hsecond := masked_product_integral_le μ (fun i ω => b i (y ω))
    (fun i ω => a i (x ω)) (fun i => (hb i).comp hy) (fun i => (ha i).comp hx)
    H₂ hH₂ δ hi₂ haint
  simp_rw [mul_comm (b _ _) (a _ _)] at hsecond
  have hm₁ : Measurable (fun ω => ∑' i,
      (H₁ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω) :=
    Measurable.tsum (fun i => (((ha i).comp hx).mul ((hb i).comp hy)).indicator (hH₁ i))
  apply (lintegral_mono_ae hc).trans
  have hm : Measurable (fun ω => r + ∑' i,
      (H₁ i).indicator (fun ω => a i (x ω) * b i (y ω)) ω) := measurable_const.add hm₁
  rw [lintegral_add_left hm, lintegral_add_left
    (measurable_const : Measurable (fun _ : Ω => r))]
  simpa using add_le_add (add_le_add le_rfl hfirst) hsecond



end ContinuousCircleWeight

end

end OAI
