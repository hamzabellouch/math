import OAI.Analysis.TriangularHilbert.GridLine

namespace OAI

universe uE

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

def closedBox (M : ℝ) : Set (ℝ×ℝ) := Set.Icc (-M) M ×ˢ Set.Icc (-M) M
lemma mem_closedBox (M : ℝ) (z : ℝ×ℝ) : z ∈ closedBox M ↔ |z.1| ≤ M ∧ |z.2| ≤ M := by
  simp only [closedBox,Set.mem_prod,Set.mem_Icc,abs_le]
lemma measurableSet_closedBox (M : ℝ) : MeasurableSet (closedBox M) := measurableSet_Icc.prod measurableSet_Icc
lemma isCompact_closedBox (M : ℝ) : IsCompact (closedBox M) := isCompact_Icc.prod isCompact_Icc
lemma volume_closedBox_ne_top (M : ℝ) : volume (closedBox M) ≠ ⊤ := (isCompact_closedBox M).measure_ne_top

def BoxSupport {E : Type uE} [Zero E] (f : ℝ×ℝ → E) (M : ℝ) : Prop :=
  ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ |z.2| ≤ M

lemma compactSupport_box {E : Type uE} [Zero E] (f : ℝ×ℝ → E) (hf : HasCompactSupport f) :
    ∃ M > 0, BoxSupport f M := by
  obtain ⟨M,hM,hm⟩ := hf.isBounded.exists_pos_norm_le
  refine ⟨M,hM,fun z hz => ?_⟩
  have hb := hm z (subset_tsupport f hz)
  have hleft : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hright : |z.2| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le z
  exact ⟨hleft.trans hb,hright.trans hb⟩

lemma sampled_cubic_tendsto (f : ℝ×ℝ → ℂ) (hf : Continuous f) {M C : ℝ}
    (hs : BoxSupport f M) (hC : 0 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C)
    {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (hh1 : ∀ n, h n ≤ 1) (ht : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z : ℝ×ℝ, ‖f (gridSquare (h n) z)‖^3) atTop (𝓝 (∫ z : ℝ×ℝ, ‖f z‖^3)) := by
  let b : ℝ×ℝ → ℝ := (closedBox (M+1)).indicator (fun _ => C^3)
  apply tendsto_integral_of_dominated_convergence b
  · intro n
    exact (((hf.measurable.comp (measurable_gridSquare (h n))).norm).pow_const 3).aestronglyMeasurable
  · exact (integrableOn_const (μ := volume) (s := closedBox (M+1)) (C := C^3)
      (volume_closedBox_ne_top _)).integrable_indicator (measurableSet_closedBox _)
  · intro n
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    by_cases hz : f (gridSquare (h n) z) = 0
    · simp only [hz,norm_zero,zero_pow (by norm_num : 3 ≠ 0),b]
      exact Set.indicator_nonneg (fun _ _ => pow_nonneg hC _) _
    · dsimp only [b]
      rw [Set.indicator_of_mem ((mem_closedBox _ _).mpr (sampled_support f (hh n) (hh1 n) hs z hz))]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb _) _
  · filter_upwards [] with z
    exact (((hf.tendsto _).comp (tendsto_gridSquare hh ht z)).norm).pow 3
end
end TriangularHilbert
end

end OAI
