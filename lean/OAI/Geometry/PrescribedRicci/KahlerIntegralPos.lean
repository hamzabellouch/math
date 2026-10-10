import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.KahlerLocalL2Comparison
import OAI.Geometry.PrescribedRicci.KahlerVolumeMeasure

namespace OAI

/-! Kahler Integral Pos. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma integral_pos (g : KaehlerMetric A) {f : X → ℝ} (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) {x : X} (hx : 0 < f x) : 0 < g.integral f := by
  obtain ⟨i,hi⟩ : ∃ i : Fin A.count, 0 < (chartPartition i).value x := by
    by_contra! hh
    have hsum := Finset.sum_nonpos (s:=Finset.univ) (f:=fun i : Fin A.count => (chartPartition i).value x) (fun i _ => hh i)
    rw [chartPartition_sum] at hsum
    linarith
  let F : X → ℝ := fun y => (chartPartition i).value y * f y
  have hF : Continuous F := (chartPartition i).continuous.fun_mul hf
  have hFs : tsupport F ⊆ (A.chart i).source := tsupport_mul_subset_left.trans (chartPartition_support i)
  obtain ⟨hl,hc,ht⟩ := localizeFunction_continuous_compact i hF hFs
  let H : Coordinates d → ℝ := fun z => localizeFunction i F z * g.volumeCoefficient i z
  have hH : Continuous H := continuous_real_mul_on_tsupport hl (fun z hz =>
    ((g.volumeCoefficient_smooth i).continuousOn z (ht hz)).continuousAt ((A.chart i).open_target.mem_nhds (ht hz)))
  have hHn (z : Coordinates d) : 0 ≤ H z := by
    by_cases hz : z ∈ (A.chart i).target
    · dsimp [H,localizeFunction]; rw [ite_eq_left hz]
      exact mul_nonneg (mul_nonneg (chartPartition_nonneg i _) (hn _)) (g.volumeCoefficient_pos i hz).le
    · simp [H,localizeFunction,hz]
  have hxs : x ∈ (A.chart i).source := chartPartition_support i (subset_tsupport _ (ne_of_gt hi))
  have hz := (A.chart i).mapsTo hxs
  have hHx : 0 < H ((A.chart i) x) := by
    dsimp only [H,localizeFunction]
    rw [ite_eq_left hz,(A.chart i).left_inv hxs]
    exact mul_pos (mul_pos hi hx) (g.volumeCoefficient_pos i hz)
  have hI : 0 < g.chartIntegral i F := by
    rw [g.chartIntegral_eq_localize]
    exact hH.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right hHn (ne_of_gt hHx)
  apply hI.trans_le
  change g.chartIntegral i F ≤ ∑ j, g.chartIntegral j (fun y => (chartPartition j).value y*f y)
  apply Finset.single_le_sum (f:=fun j : Fin A.count => g.chartIntegral j (fun y => (chartPartition j).value y*f y)) _ (Finset.mem_univ i)
  intro j _
  apply setIntegral_nonneg (A.chart j).open_target.measurableSet
  intro z hz
  exact mul_nonneg (mul_nonneg (chartPartition_nonneg j _) (hn _)) (g.volumeCoefficient_pos j hz).le

variable [MeasurableSpace X] [BorelSpace X]

instance volumeMeasure_openPos (g : KaehlerMetric A) : g.volumeMeasure.IsOpenPosMeasure where
  open_pos U hU hUn := by
    obtain ⟨x,hx⟩ := hUn
    obtain ⟨f,hf1,_,hfs,hfn⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
      (isCompact_singleton (x:=x)) hU (singleton_subset_iff.mpr hx)
    have hpos := g.integral_pos f.continuous (fun y => (hfn y).1)
      (show 0 < f x by rw [hf1 (mem_singleton x)]; norm_num)
    intro hzero
    have hae : f =ᵐ[g.volumeMeasure] (fun _ => (0:ℝ)) := by
      apply ae_iff.mpr
      apply measure_mono_null _ hzero
      intro y hy
      exact hfs (subset_tsupport f hy)
    have hz : g.integral f = 0 := by
      rw [← g.integral_volumeMeasure f.continuous, integral_congr_ae hae, MeasureTheory.integral_zero]
    linarith

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
