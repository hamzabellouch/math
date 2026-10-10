import OAI.Analysis.CircleDomains.Modulus.SimpleArcLength
import OAI.Analysis.CircleDomains.Topology.DyadicOpenCover
import Mathlib.Topology.UniformSpace.Compact

namespace OAI

/-! Every continuous path has image Hausdorff length at most its metric
variation. Small dyadic images supply the covers in the definition. -/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

theorem exists_small_dyadic_images {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ i : Fin (2 ^ n),
      ediam (γ '' Icc (dyadicLeft n i) (dyadicRight n i)) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous γ.continuous) ε hε
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hz : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hp)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hz).2 δ hδ).exists
  refine ⟨n, fun i => ediam_le ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hd ((dyadicCell_dist_le n i hs ht).trans_lt hn)).le

theorem path_hausdorff_length_le_variation {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (γ : C(PathTime, X)) :
    (μH[1] : Measure X) (range γ) ≤ eVariationOn γ univ := by
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  choose k hk using fun n => exists_small_dyadic_images γ (hr n)
  let A : ∀ n : ℕ, Fin (2 ^ k n) → Set X :=
    fun n i => γ '' Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)
  have hcover (n : ℕ) : range γ ⊆ ⋃ i, A n i := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := exists_dyadicCell_mem (k n) t
    exact mem_iUnion.mpr ⟨i, t, hi, rfl⟩
  have hrad : Tendsto (fun n => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
    simpa only [r, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
  apply (Measure.hausdorffMeasure_le_liminf_sum 1 (range γ)
    (fun n => ENNReal.ofReal (r n)) hrad A
    (Eventually.of_forall hk) (Eventually.of_forall hcover)).trans
  apply liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [] with n
  simp only [ENNReal.rpow_one]
  calc
    ∑ i, ediam (A n i) ≤
        ∑ i : Fin (2 ^ k n), eVariationOn γ (Icc (dyadicLeft (k n) i) (dyadicRight (k n) i)) := by
      apply Finset.sum_le_sum
      intro i _
      apply ediam_le
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      exact eVariationOn.edist_le γ hs ht
    _ = _ := sum_dyadic_variations γ (k n)

end CircleDomainRigidity

end

end OAI
