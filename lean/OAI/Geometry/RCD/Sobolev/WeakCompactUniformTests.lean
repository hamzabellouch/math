import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence
import OAI.Geometry.RCD.Sobolev.EverySubsequenceEventual
import OAI.Geometry.RCD.Coordinates.NormalizedUniformMean
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-! # Weak convergence is uniform over bounded Lipschitz tests on a common compact support -/

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

private theorem bounded_test (Y : Type*) [MetricSpace Y] (f : Y → ℝ)
    (hf : Continuous f) (hb : ∀ y, |f y| ≤ 1) :
    ∃ F : Y →ᵇ ℝ, ∀ y, F y=f y := by
  refine ⟨BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ 2 ?_,fun _ => rfl⟩
  intro x y
  change |f x-f y| ≤ 2
  have ht := abs_sub_le (f x) 0 (f y)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  linarith [hb x,hb y]

theorem weak_compact_uniform_tests {Y : Type*} [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {P : ℕ → ProbabilityMeasure Y} {Q : ProbabilityMeasure Y}
    (hweak : Tendsto P atTop (𝓝 Q)) {A : Set Y} (hA : IsCompact A)
    (hP : ∀ k, ∀ᵐ x ∂(P k : Measure Y), x ∈ A)
    (hQ : ∀ᵐ x ∂(Q : Measure Y), x ∈ A) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ∀ f : Y → ℝ, LipschitzWith 1 f → (∀ x, |f x| ≤ 1) →
      |(∫ x, f x ∂(P k : Measure Y)) - ∫ x, f x ∂(Q : Measure Y)| ≤ δ := by
  classical
  by_contra hnot
  obtain ⟨α,hα,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hnot)
  have hex (k : ℕ) : ∃ f : Y → ℝ, LipschitzWith 1 f ∧ (∀ x, |f x| ≤ 1) ∧
      δ < |(∫ x, f x ∂(P (α k) : Measure Y)) - ∫ x, f x ∂(Q : Measure Y)| := by
    simpa only [not_forall,not_le,exists_prop] using hbad k
  choose f hf hb hfail using hex
  obtain ⟨g,β,hβ,hg,hgb,hunif⟩ := exists_lipschitz_subsequence_on_compact hA f 1 1 hf
    (fun k x _ => hb k x)
  let g' : Y → ℝ := fun x => max (-1) (min 1 (g x))
  have hg' : Continuous g' := continuous_const.max (continuous_const.min hg.continuous)
  have hg'b (x : Y) : |g' x| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hgeq (x : Y) (hx : x ∈ A) : g' x=g x := by
    have h := abs_le.mp (hgb x hx)
    exact (max_eq_right (h.1.trans_eq (min_eq_right h.2).symm)).trans (min_eq_right h.2)
  obtain ⟨G,hG⟩ := bounded_test Y g' hg' hg'b
  have hclose {ν : ℕ → ProbabilityMeasure Y}
      (hν : ∀ k, ∀ᵐ x ∂(ν k : Measure Y), x ∈ A) :
      Tendsto (fun k => ∫ x, f (β k) x - G x ∂(ν k : Measure Y)) atTop (𝓝 0) := by
    have ht := normalized_mean_tendsto_zero (fun k => (ν k : Measure Y))
      (fun _ => by simp [Measure.real]) (fun k x => f (β k) x-G x) ?_
    · simpa only [Measure.real,measure_univ,ENNReal.toReal_one,inv_one,one_mul] using ht
    · intro η hη
      filter_upwards [hunif η hη] with k hk
      filter_upwards [hν k] with x hx
      rw [hG,hgeq x hx]
      exact (hk x hx).le
  have h1 := hclose (fun k => hP (α (β k)))
  have h2 := hclose (ν := fun _ => Q) (fun _ => hQ)
  have h3 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (hweak.comp (hα.comp hβ).tendsto_atTop) G
  have hfi (k : ℕ) (ν : ProbabilityMeasure Y) : Integrable (f k) (ν : Measure Y) :=
    (integrable_const (1 : ℝ)).mono' (hf k).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb k x)
  have heq (k : ℕ) (ν : ProbabilityMeasure Y) :
      (∫ x, f k x-G x ∂(ν : Measure Y))=
        (∫ x, f k x ∂(ν : Measure Y)) - ∫ x, G x ∂(ν : Measure Y) :=
    integral_sub (hfi k ν) (G.integrable (μ := (ν : Measure Y)))
  simp only [heq] at h1 h2
  have hconst : Tendsto (fun _ : ℕ => ∫ x, G x ∂(Q : Measure Y)) atTop
      (𝓝 (∫ x, G x ∂(Q : Measure Y))) := tendsto_const_nhds
  have hall := (h1.add (h3.sub hconst)).sub h2
  have ht : Tendsto (fun k => (∫ x, f (β k) x ∂(P (α (β k)) : Measure Y)) -
      ∫ x, f (β k) x ∂(Q : Measure Y)) atTop (𝓝 0) := by
    convert hall using 1 <;> simp
  have hta := ht.abs
  simp only [abs_zero] at hta
  obtain ⟨k,hk⟩ := (hta.eventually (Iio_mem_nhds hδ)).exists
  exact (hfail (β k)).not_gt hk

end RegularPointCoordinates

end

end OAI
