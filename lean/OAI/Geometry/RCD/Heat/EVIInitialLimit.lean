import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI

/-! # The initial endpoint of an integrated evolution inequality -/

open Set Filter MeasureTheory Metric
open scoped Topology
namespace RegularPointCoordinates

theorem integrated_inequality_initial_limit {D G : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hD : ContinuousOn D (Icc 0 b)) (hG : ContinuousOn G (Icc 0 b))
    (h : ∀ a : ℝ, 0 < a → a ≤ b → D b-D a ≤ ∫ t in a..b, G t) :
    D b-D 0 ≤ ∫ t in 0..b, G t := by
  have hDc : ContinuousWithinAt D (Ioi 0) 0 :=
    ((hD 0 ⟨le_rfl,hb.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hb)).mono Ioi_subset_Ici_self
  have hGi : IntegrableOn G (uIcc 0 b) volume := by
    rw [uIcc_of_le hb.le]
    exact hG.integrableOn_Icc
  have hJ := intervalIntegral.continuousOn_primitive_interval_left hGi
  rw [uIcc_of_le hb.le] at hJ
  have hJc : ContinuousWithinAt (fun a => ∫ t in a..b, G t) (Ioi 0) 0 :=
    ((hJ 0 ⟨le_rfl,hb.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hb)).mono Ioi_subset_Ici_self
  apply le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hDc.tendsto) hJc.tendsto
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hb)] with a ha hab
  exact h a ha hab.le

theorem nonneg_initial_of_integral_nonneg {G : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hG : ContinuousOn G (Icc 0 T))
    (h : ∀ t : ℝ, 0 < t → t ≤ T → 0 ≤ ∫ s in 0..t, G s) : 0 ≤ G 0 := by
  by_contra hn
  have hn : G 0 < 0 := lt_of_not_ge hn
  have hnear := (hG 0 ⟨le_rfl,hT.le⟩).eventually
    (Iio_mem_nhds (by linarith : G 0 < G 0/2))
  obtain ⟨δ,hδ,hδG⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let t := min δ T/2
  have ht : 0 < t := div_pos (lt_min hδ hT) (by norm_num)
  have htδ : t < δ := by dsimp only [t]; linarith [min_le_left δ T]
  have htT : t ≤ T := by dsimp only [t]; linarith [min_le_right δ T]
  have hi : IntervalIntegrable G volume 0 t :=
    (hG.mono (Icc_subset_Icc le_rfl htT)).intervalIntegrable_of_Icc ht.le
  have hb : (∫ s in 0..t, G s) ≤ t*(G 0/2) := by
    calc
      _ ≤ ∫ s in 0..t, G 0/2 := by
        apply intervalIntegral.integral_mono_on ht.le hi (continuous_const.intervalIntegrable 0 t)
        intro s hs
        apply le_of_lt
        apply hδG
        refine ⟨?_,⟨hs.1,hs.2.trans htT⟩⟩
        rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hs.1]
        exact hs.2.trans_lt htδ
      _ = _ := by rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have hp : t*(G 0/2) < 0 := mul_neg_of_pos_of_neg ht (by linarith)
  linarith [h t ht htT]

end RegularPointCoordinates

end OAI
