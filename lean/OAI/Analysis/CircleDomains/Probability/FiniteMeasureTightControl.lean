import OAI.Analysis.CircleDomains.Probability.MeasureQuadraticSum
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace OAI

/-! The tightness estimate in the measure-modulus duality argument.
A finite Borel reference measure admits arbitrarily cheap L² densities
which charge every measure outside a compact set by at least one. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_finiteMeasure_control
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (T : Set (FiniteMeasure Z)) (h : Z → ℝ≥0∞), IsCompact T ∧ Measurable h ∧
      (∫⁻ z, h z ^ 2 ∂σ) < ε ∧
      ∀ v : FiniteMeasure Z, v ∉ T → 1 ≤ ∫⁻ z, h z ∂(v : Measure Z) := by
  classical
  obtain ⟨b,hb,hbsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' (Option ℕ)
  obtain ⟨δ,hδ,hδsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (measure_ne_top σ univ) (hb none).ne'
  let c : ℝ≥0 := min δ 1
  have hc : 0 < c := lt_min hδ zero_lt_one
  have hc2 : c ^ 2 ≤ δ := by
    have h1 : c ≤ 1 := min_le_right _ _
    have hδ' : c ≤ δ := min_le_left _ _
    calc
      c ^ 2 = c*c := pow_two c
      _ ≤ c := mul_le_of_le_one_right (show (0 : ℝ≥0) ≤ c from zero_le) h1
      _ ≤ δ := hδ'
  have hcsmall : (c : ℝ≥0∞)^2 * σ univ < b none := by
    exact (mul_le_mul_left (by exact_mod_cast hc2) _).trans_lt hδsmall
  let w (n : ℕ) : ℝ≥0 := n+1
  have hw (n : ℕ) : 0 < w n := by simp [w]
  have he (n : ℕ) : ∃ d : ℝ≥0, 0 < d ∧
      (d : ℝ≥0∞) * (w n : ℝ≥0∞)^2 < b (some n) := by
    exact ENNReal.exists_nnreal_pos_mul_lt (by simp) (hb (some n)).ne'
  choose d hd hdsmall using he
  have hK (n : ℕ) : ∃ K : Set Z, IsCompact K ∧ σ Kᶜ < d n := by
    obtain ⟨K,_,hK,hsmall⟩ := (MeasurableSet.univ : MeasurableSet (univ : Set Z)).exists_isCompact_sdiff_lt (μ := σ) (ε := (d n : ℝ≥0∞))
      (measure_ne_top σ univ) (by exact_mod_cast (hd n).ne')
    exact ⟨K,hK,by simpa only [← compl_eq_univ_sdiff] using hsmall⟩
  choose K hK hKsmall using hK
  let g : Option ℕ → Z → ℝ≥0∞
    | none => fun _ => c
    | some n => (K n)ᶜ.indicator (fun _ => w n)
  have hgm (i : Option ℕ) : Measurable (g i) := by
    cases i with
    | none => exact measurable_const
    | some n => exact measurable_const.indicator (hK n).measurableSet.compl
  have hge (i : Option ℕ) : (∫⁻ z, g i z ^ 2 ∂σ) < b i := by
    cases i with
    | none => simpa [g,lintegral_const] using hcsmall
    | some n =>
      have heq : (fun z => g (some n) z ^ 2) =
          (K n)ᶜ.indicator (fun _ => (w n : ℝ≥0∞)^2) := by
        funext z
        by_cases hz : z ∈ (K n)ᶜ <;> simp [g,hz]
      rw [heq,lintegral_indicator (hK n).measurableSet.compl]
      simp only [lintegral_const,Measure.restrict_apply_univ]
      exact (mul_le_mul_right (hKsmall n).le _).trans_lt
        (by simpa only [mul_comm] using hdsmall n)
  obtain ⟨h,hh,hdom,henergy⟩ := exists_quadratic_sum_density σ g hgm
  let T : Set (FiniteMeasure Z) :=
    {v | v.mass ≤ c⁻¹ ∧ ∀ n, v (K n)ᶜ ≤ (w n)⁻¹}
  have hu : Tendsto (fun n => (w n)⁻¹) atTop (𝓝 0) := by
    simpa [w,Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hTc : IsCompact T :=
    isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le c⁻¹ hu hK (Or.inl inferInstance)
  refine ⟨T,h,hTc,hh,?_,?_⟩
  · rw [henergy]
    exact (ENNReal.tsum_le_tsum (fun i => (hge i).le)).trans_lt hbsum
  · intro v hv
    by_contra hn
    have hi : (∫⁻ z, h z ∂(v : Measure Z)) < 1 := lt_of_not_ge hn
    have hm : v.mass ≤ c⁻¹ := by
      have hb₀ : (∫⁻ z, g none z ∂(v : Measure Z)) ≤ 1 :=
        (show (∫⁻ z, g none z ∂(v : Measure Z)) ≤ ∫⁻ z, h z ∂(v : Measure Z)
          from lintegral_mono (hdom none)).trans hi.le
      have hb : (c : ℝ≥0∞) * (v : Measure Z) univ ≤ 1 := by
        simpa only [g,lintegral_const] using hb₀
      rw [← FiniteMeasure.ennreal_mass] at hb
      have hb' : c * v.mass ≤ 1 := by exact_mod_cast hb
      have he : v.mass ≤ 1 / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb')
      simpa only [one_div] using he
    have ht (n : ℕ) : v (K n)ᶜ ≤ (w n)⁻¹ := by
      have hb := (lintegral_mono (hdom (some n)) (μ := (v : Measure Z))).trans hi.le
      change (∫⁻ z, (K n)ᶜ.indicator (fun _ => (w n : ℝ≥0∞)) z ∂(v : Measure Z)) ≤ 1 at hb
      rw [lintegral_indicator (hK n).measurableSet.compl,lintegral_const,
        Measure.restrict_apply_univ,← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hb
      have hb' : w n * v (K n)ᶜ ≤ 1 := by exact_mod_cast hb
      have he : v (K n)ᶜ ≤ 1 / w n := (le_div_iff₀ (hw n)).mpr (by simpa only [mul_comm] using hb')
      simpa only [one_div] using he
    exact hv ⟨hm,ht⟩

end CircleDomainRigidity

end

end OAI
