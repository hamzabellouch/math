import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PointLaw01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope1
open scoped Topology BigOperators
open Filter MeasureTheory Set
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace SourcePointLaw
noncomputable section
open scoped Topology BigOperators
open Filter MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [Module ℚ≥0 E]

 

theorem residue_point_law
    (P : ℕ → ℤ → E) (d : ℕ) (hd : 0 < d) (r : ℤ)
    (hr : 0 ≤ r ∧ r < (d : ℤ)) (f : ℝ → E)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hloc : ∀ x ∈ Icc (0 : ℝ) 1, ∀ ε > 0,
      ∀ᶠ α : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop,
      ∀ a b : ℝ, 0 ≤ a → a ≤ x → x ≤ b → b ≤ 1 → b - a = α →
        ‖(𝔼 n ∈ residueInterval d r (a * N) (b * N), P N n) - f x‖ < ε) :
    Tendsto (fun N => windowSum P d r N 0 1) atTop
      (𝓝 ((d : ℝ)⁻¹ • ∫ x in (0 : ℝ)..1, f x)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← intervalIntegral.integral_smul]
  apply tendsto_of_local_interval_law atTop (windowSum P d r)
    (fun x => (d : ℝ)⁻¹ • f x)
  · intro N a b c _ hab hbc _
    exact windowSum_add P d r N a b c hab hbc
  · exact hf.const_smul _
  · intro x hx ε hε
    have hη : 0 < ε * (d : ℝ) / 4 := by positivity
    obtain ⟨δ, hδ, hδp⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hloc x hx _ hη)
    refine ⟨δ, hδ, ?_⟩
    intro a b ha hab hb hax hxb hlen
    have hlocal := hδp ⟨sub_pos.mpr hab, hlen⟩
    have hm := residueInterval_card_tendsto d hd r hr a b hab.le
    have hup : ∀ᶠ N : ℕ in atTop,
        ((residueInterval d r (a * N) (b * N)).card : ℝ) / N <
          2 * (b - a) / (d : ℝ) :=
      (tendsto_order.mp hm).2 _ (by rw [mul_div_assoc]; have : 0 < (b-a)/(d:ℝ) := div_pos (sub_pos.mpr hab) hdR; linarith)
    have hsm := hm.smul (tendsto_const_nhds (x := f x))
    have heps : 0 < ε * (b - a) / 2 := by positivity
    have herr := (Metric.tendsto_nhds.mp hsm) _ heps
    filter_upwards [hlocal, hup, herr] with N hN hupper herror
    have hmass : 0 ≤ ((residueInterval d r (a * N) (b * N)).card : ℝ) / N :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have havg := hN a b ha hax hxb hb rfl
    rw [windowSum_eq]
    have hscale : (b - a) • ((d : ℝ)⁻¹ • f x) = ((b - a)/(d : ℝ)) • f x := by
      simp only [smul_smul, div_eq_mul_inv]
    rw [hscale]
    calc
      _ ≤ ‖(((residueInterval d r (a * N) (b * N)).card : ℝ) / N) •
          ((𝔼 n ∈ residueInterval d r (a * N) (b * N), P N n) - f x)‖ +
          ‖(((residueInterval d r (a * N) (b * N)).card : ℝ) / N) • f x -
            ((b - a)/(d : ℝ)) • f x‖ := by
        rw [smul_sub]
        exact (show _ from norm_add_le _ _).trans_eq' (congrArg norm (by abel))
      _ ≤ (2 * (b - a) / (d : ℝ)) * (ε * (d : ℝ) / 4) + ε * (b - a) / 2 := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hmass]
          exact mul_le_mul hupper.le havg.le (norm_nonneg _) (by positivity)
        · simpa only [dist_eq_norm] using herror.le
      _ = ε * (b - a) := by field_simp; ring

end
end SourcePointLaw

namespace SourcePointLaw
noncomputable section
open scoped Topology BigOperators
open Filter MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
omit [NormedSpace ℝ E] in
lemma residueInterval_sum (d : ℕ) (hd : 0 < d) (a b : ℝ) (F : ℤ → E) :
    ∑ r ∈ Finset.Ico (0 : ℤ) (d : ℤ), ∑ n ∈ residueInterval d r a b, F n =
      ∑ n ∈ Finset.Ico ⌈a⌉ ⌈b⌉, F n := by
  apply Finset.sum_fiberwise_of_maps_to
  intro n hn
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg n hd'.ne', Int.emod_lt_of_pos n hd'⟩

omit [NormedSpace ℝ E] in
lemma sum_int_Ico_zero_nat (N : ℕ) (F : ℤ → E) :
    ∑ n ∈ Finset.Ico (0 : ℤ) (N : ℤ), F n = ∑ n ∈ Finset.range N, F n := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast hn⟩
  · intro a ha b hb hab
    exact_mod_cast hab
  · intro n hn
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ico.mp hn
    refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hn0⟩
    simp only [Finset.mem_range]
    have : (n.toNat : ℤ) < (N : ℤ) := by simpa only [Int.toNat_of_nonneg hn0] using hnN
    exact_mod_cast this
  · intro n hn
    rfl

 

lemma sum_windowSum (P : ℕ → ℤ → E) (d : ℕ) (hd : 0 < d) (N : ℕ) :
    ∑ r ∈ Finset.Ico (0 : ℤ) (d : ℤ), windowSum P d r N 0 1 =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, P N n := by
  simp only [windowSum, ← Finset.smul_sum]
  rw [residueInterval_sum d hd]
  simp only [zero_mul, one_mul, Int.ceil_zero, Int.ceil_natCast]
  rw [sum_int_Ico_zero_nat]

 

theorem global_point_law [CompleteSpace E] [Module ℚ≥0 E]
    (P : ℕ → ℤ → E) (d : ℕ) (hd : 0 < d) (f : ℤ → ℝ → E)
    (hf : ∀ r ∈ Finset.Ico (0 : ℤ) (d : ℤ), ContinuousOn (f r) (Icc (0 : ℝ) 1))
    (hloc : ∀ r ∈ Finset.Ico (0 : ℤ) (d : ℤ), ∀ x ∈ Icc (0 : ℝ) 1, ∀ ε > 0,
      ∀ᶠ α : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop,
      ∀ a b : ℝ, 0 ≤ a → a ≤ x → x ≤ b → b ≤ 1 → b - a = α →
        ‖(𝔼 n ∈ residueInterval d r (a * N) (b * N), P N n) - f r x‖ < ε) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, P N n) atTop
      (𝓝 ((d : ℝ)⁻¹ • ∑ r ∈ Finset.Ico (0 : ℤ) (d : ℤ), ∫ x in (0 : ℝ)..1, f r x)) := by
  simpa only [sum_windowSum P d hd, Finset.smul_sum] using
    tendsto_finsetSum (Finset.Ico (0 : ℤ) (d : ℤ)) (fun r hr =>
      residue_point_law P d hd r (Finset.mem_Ico.mp hr) (f r) (hf r hr) (hloc r hr))

end
end SourcePointLaw

namespace SourcePointLaw
noncomputable section
open scoped Topology BigOperators
open Filter MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sum_windowSum_fin (P : ℕ → ℤ → E) (d : ℕ) (hd : 0 < d) (N : ℕ) :
    ∑ r : Fin d, windowSum P d r.val N 0 1 =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, P N n := by
  calc
    _ = ∑ r ∈ Finset.range d, windowSum P d r N 0 1 := (Finset.sum_range _).symm
    _ = ∑ r ∈ Finset.Ico (0 : ℤ) (d : ℤ), windowSum P d r N 0 1 :=
      (sum_int_Ico_zero_nat d (fun r => windowSum P d r N 0 1)).symm
    _ = _ := sum_windowSum P d hd N

 

theorem global_point_law_fin [CompleteSpace E] [Module ℚ≥0 E]
    (P : ℕ → ℤ → E) (d : ℕ) (hd : 0 < d) (f : Fin d → ℝ → E)
    (hf : ∀ r, ContinuousOn (f r) (Icc (0 : ℝ) 1))
    (hloc : ∀ r, ∀ x ∈ Icc (0 : ℝ) 1, ∀ ε > 0,
      ∀ᶠ α : ℝ in 𝓝[>] 0, ∀ᶠ N : ℕ in atTop,
      ∀ a b : ℝ, 0 ≤ a → a ≤ x → x ≤ b → b ≤ 1 → b - a = α →
        ‖(𝔼 n ∈ residueInterval d r.val (a * N) (b * N), P N n) - f r x‖ < ε) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, P N n) atTop
      (𝓝 ((d : ℝ)⁻¹ • ∑ r : Fin d, ∫ x in (0 : ℝ)..1, f r x)) := by
  have hres (r : Fin d) := residue_point_law P d hd r.val
    (show 0 ≤ (r.val : ℤ) ∧ (r.val : ℤ) < (d : ℤ) from
      ⟨Int.natCast_nonneg _, by exact_mod_cast r.isLt⟩) (f r) (hf r) (hloc r)
  simpa only [sum_windowSum_fin P d hd, Finset.smul_sum] using
    tendsto_finsetSum Finset.univ (fun r _ => hres r)

end
end SourcePointLaw

 

open scoped Topology BigOperators BoundedContinuousFunction ENNReal
open MeasureTheory Set Filter

namespace SourcePointLaw
noncomputable section

def betaMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance betaMeasure_probability : IsProbabilityMeasure betaMeasure where
  measure_univ := by simp [betaMeasure]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

 

def betaImage (μ : ProbabilityMeasure X) (T : ℝ × X → Y) (hT : Measurable T) :
    ProbabilityMeasure Y :=
  ⟨Measure.map T (betaMeasure.prod (μ : Measure X)),
    (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance⟩

variable [TopologicalSpace Y] [OpensMeasurableSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

 

theorem integral_betaImage (μ : ProbabilityMeasure X) (T : ℝ × X → Y)
    (hT : Measurable T) (F : Y →ᵇ E) :
    ∫ y, F y ∂(betaImage μ T hT : Measure Y) =
      ∫ β in (0 : ℝ)..1, ∫ x, F (T (β, x)) ∂(μ : Measure X) := by
  change (∫ y, F y ∂Measure.map T (betaMeasure.prod (μ : Measure X))) = _
  rw [integral_map hT.aemeasurable F.continuous.measurable.aestronglyMeasurable]
  have hi : Integrable (fun z : ℝ × X => F (T z)) (betaMeasure.prod (μ : Measure X)) :=
    (integrable_const ‖F‖).mono'
      (F.continuous.measurable.comp hT).aestronglyMeasurable
      (Eventually.of_forall (fun z => F.norm_coe_le_norm (T z)))
  rw [integral_prod _ hi]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_Icc_eq_integral_Ioc

end
end SourcePointLaw

namespace SourcePointLaw
noncomputable section
open scoped Topology BigOperators BoundedContinuousFunction ENNReal
open MeasureTheory Set Filter

variable {I Y : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Y]

 
def uniformMixture (μ : I → ProbabilityMeasure Y) : ProbabilityMeasure Y :=
  ⟨(Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, (μ i : Measure Y), by
    constructor
    simp [Measure.smul_apply, Finset.sum_apply, ENNReal.inv_mul_cancel,
      Fintype.card_ne_zero]⟩

variable [TopologicalSpace Y] [OpensMeasurableSpace Y]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

lemma integral_uniformMixture (μ : I → ProbabilityMeasure Y) (F : Y →ᵇ E) :
    ∫ y, F y ∂(uniformMixture μ : Measure Y) =
      (Fintype.card I : ℝ)⁻¹ • ∑ i, ∫ y, F y ∂(μ i : Measure Y) := by
  change (∫ y, F y ∂((Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, (μ i : Measure Y))) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i hi
    exact F.integrable _

end
end SourcePointLaw

end RawSuccessInlineScope1
end

end OAI
