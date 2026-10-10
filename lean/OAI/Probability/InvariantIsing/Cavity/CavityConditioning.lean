import OAI.Probability.InvariantIsing.Cavity.CavityGramProbability
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! Conditioning on the nondegenerate Gram event does not change the
limit of bounded observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_conditioning_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (f : Ω → Ω') (hf : Measurable f)
    (s : Set Ω') (hs : MeasurableSet s) :
    (cond μ (f ⁻¹' s)).map f = cond (μ.map f) s := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul _ hf.aemeasurable, Measure.map_apply hf hs,
    Measure.restrict_map hf hs]

lemma cavity_conditioning_invariant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω) (hT : Measurable T) (hμ : μ.map T = μ)
    (s : Set Ω) (hs : MeasurableSet s) (hinv : T ⁻¹' s = s) :
    (cond μ s).map T = cond μ s := by
  have hr : (μ.restrict s).map T = μ.restrict s := by
    calc
      (μ.restrict s).map T = (μ.restrict (T ⁻¹' s)).map T := by rw [hinv]
      _ = (μ.map T).restrict s := (Measure.restrict_map hT hs).symm
      _ = μ.restrict s := by rw [hμ]
  rw [ProbabilityTheory.cond, Measure.map_smul _ hT.aemeasurable, hr]

lemma cavity_conditioning_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s)
    (hp : 0 < μ.real s) (f : Ω → ℝ) (hf : Integrable f μ)
    (M : ℝ) (hbound : ∀ x, |f x| ≤ M) :
    |(∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ| ≤ 2 * M * (1 - μ.real s) := by
  let p := μ.real s
  have hp1 : p ≤ 1 := measureReal_le_one
  have hpc : μ.real sᶜ = 1 - p := by
    simpa only [p, Measure.real, measure_univ, ENNReal.toReal_one] using
      (measureReal_compl (μ := μ) hs)
  have hA : |∫ x in s, f x ∂μ| ≤ p * M := by
    simpa only [Real.norm_eq_abs, mul_comm, p] using
      norm_setIntegral_le_of_norm_le_const (f := f) (measure_lt_top μ s)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x)
  have hB : |∫ x in sᶜ, f x ∂μ| ≤ M * (1 - p) := by
    simpa only [Real.norm_eq_abs, hpc, mul_comm] using
      norm_setIntegral_le_of_norm_le_const (f := f) (measure_lt_top μ sᶜ)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hbound x)
  have hfac : 0 ≤ p⁻¹ - 1 := by
    have hinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp).mpr hp1
    linarith
  have hmul : (p⁻¹ - 1) * p = 1 - p := by
    rw [sub_mul, inv_mul_cancel₀ hp.ne', one_mul]
  have he : (∫ x, f x ∂cond μ s) - ∫ x, f x ∂μ =
      (p⁻¹ - 1) * (∫ x in s, f x ∂μ) - ∫ x in sᶜ, f x ∂μ := by
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
      ← integral_add_compl hs hf]
    change p⁻¹ • (∫ x in s, f x ∂μ) - _ = _
    simp only [smul_eq_mul]
    ring
  rw [he]
  calc
    |(p⁻¹ - 1) * (∫ x in s, f x ∂μ) - ∫ x in sᶜ, f x ∂μ| ≤
        (p⁻¹ - 1) * |∫ x in s, f x ∂μ| + |∫ x in sᶜ, f x ∂μ| := by
      simpa only [abs_mul, abs_of_nonneg hfac] using
        abs_sub ((p⁻¹ - 1) * (∫ x in s, f x ∂μ)) (∫ x in sᶜ, f x ∂μ)
    _ ≤ (p⁻¹ - 1) * (p * M) + M * (1 - p) :=
      add_le_add (mul_le_mul_of_nonneg_left hA hfac) hB
    _ = 2 * M * (1 - p) := by rw [← mul_assoc, hmul]; ring

theorem cavity_conditioning_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n))
    (hp : Tendsto (fun n => μ.real (s n)) atTop (𝓝 1))
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (M : ℝ) (hbound : ∀ n x, |f n x| ≤ M) :
    Tendsto (fun n => (∫ x, f n x ∂cond μ (s n)) - ∫ x, f n x ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun n => 2 * M * (1 - μ.real (s n)))
  · filter_upwards [hp.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    simpa only [Real.norm_eq_abs] using
      cavity_conditioning_bound μ (s n) (hs n) hn (f n) (hf n) M (hbound n)
  · simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp).const_mul
        (2 * M)

end InvariantIsing

end

end OAI
