import OAI.Probability.InvariantIsing.Cavity.CavityFieldPath
import OAI.Probability.InvariantIsing.Spectral.SpectralFubini

namespace OAI

/-! The weighted layer-cake identity in the cavity value calculation.
Atoms of the overlap distribution are retained through the strict tail. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

def cavityTailMoment (p : OverlapPath) (r : ℝ) : ℝ :=
  ∫ s, if r < p s then p s else 0 ∂pathMeasure

lemma cavityTailMoment_eq_deficit (p : OverlapPath) (r : ℝ) :
    cavityTailMoment p r = 1 - deficit p r - r * pathMeasure.real {s | p s ≤ r} := by
  let A : Set ℝ := {s | r < p s}
  have hA : MeasurableSet A := measurableSet_lt measurable_const p.measurable
  have hI : Integrable (A.indicator p.val) pathMeasure := p.integrable.indicator hA
  have he : (fun s => max (p s - r) 0) =
      (fun s => A.indicator p.val s - r * A.indicator (fun _ => (1 : ℝ)) s) := by
    funext s
    by_cases h : r < p s
    · have h' : s ∈ A := h
      simp only [indicator_of_mem h', mul_one, max_eq_left (sub_nonneg.mpr h.le)]
    · have h' : s ∉ A := h
      simp only [indicator_of_notMem h', mul_zero, sub_self,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]
  have hcomp : Aᶜ = {s | p s ≤ r} := by ext s; simp [A]
  have hm : pathMeasure.real A = 1 - pathMeasure.real {s | p s ≤ r} := by
    have hh := measureReal_compl (μ := pathMeasure) hA
    rw [hcomp] at hh
    have hu : pathMeasure.real univ = 1 := probReal_univ
    rw [hu] at hh
    linarith
  have ht : (∫ s, max (p s - r) 0 ∂pathMeasure) =
      cavityTailMoment p r - r * pathMeasure.real A := by
    rw [he, integral_sub hI ((integrable_const (1 : ℝ)).indicator hA |>.const_mul r),
      integral_const_mul, integral_indicator_const 1 hA]
    simp only [smul_eq_mul, mul_one, cavityTailMoment, A, indicator, Set.mem_ofPred_eq]
  rw [hm] at ht
  unfold deficit
  linarith

lemma integral_pathMeasure_eq_interval (f : ℝ → ℝ) :
    (∫ r, f r ∂pathMeasure) = ∫ r in 0..1, f r := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

lemma cavity_weighted_primitive_fubini (p : OverlapPath) (f : ℝ → ℝ)
    (hf : Continuous f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ r, |f r| ≤ M) :
    (∫ s, p s * (∫ r in 0..p s, f r) ∂pathMeasure) =
      ∫ r in 0..1, f r * cavityTailMoment p r := by
  let K : ℝ → ℝ → ℝ := fun r s => if r < p s then p s * f r else 0
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min (0 : ℝ) 1) (max 0 1)))
    infer_instance
  have hm : Measurable (Function.uncurry K) := Measurable.ite
    (measurableSet_lt measurable_fst (p.measurable.comp measurable_snd))
    ((p.measurable.comp measurable_snd).mul (hf.measurable.comp measurable_fst)) measurable_const
  have hi : Integrable (Function.uncurry K)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod pathMeasure) := by
    apply (integrable_const M).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.uncurry, K]
      split_ifs
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p.nonneg _)]
        exact (mul_le_mul_of_nonneg_left (hb z.1) (p.nonneg z.2)).trans
          (mul_le_of_le_one_left hM (p.le_one z.2))
      · simpa using hM)
  have hinner (r : ℝ) : (∫ s, K r s ∂pathMeasure) = f r * cavityTailMoment p r := by
    rw [cavityTailMoment, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun s => by by_cases h : r < p s <;> simp [K, h, mul_comm])
  have houter (s : ℝ) : (∫ r in 0..1, K r s) = p s * (∫ r in 0..p s, f r) := by
    calc
      _ = ∫ r in 0..1, p s * ({r | r ≤ p s}.indicator f r) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [volume.ae_ne (p s)] with r hr
        intro _
        by_cases h : r < p s
        · simp [K, h, h.le]
        · have h' : ¬r ≤ p s := fun hh => hr (le_antisymm hh (le_of_not_gt h))
          simp [K, h, h']
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_indicator ⟨p.nonneg s, p.le_one s⟩]
  have hs := intervalIntegral_integral_swap hi
  simp_rw [hinner, houter] at hs
  exact hs.symm

end InvariantIsing

end

end OAI
