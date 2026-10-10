import OAI.Geometry.EinsteinFour.FiniteExceptionalMeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Angular distance starting at zero needs a derivative bound only between its extreme values. -/
namespace PositiveEinsteinFour.Geometry
open Set

theorem bounded_angle_le_of_deriv_le (f : ℝ → ℝ) (a b B C : ℝ) (E : Finset ℝ)
    (hab : a ≤ b) (hC : 0 ≤ C) (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0)
    (hpos : ∀ t ∈ Icc a b, 0 ≤ f t) (hB : f b ≤ B)
    (hd : ∀ t ∈ Ioo a b, t ∉ E → 0 < f t → f t < B → DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo a b, t ∉ E → 0 < f t → f t < B → deriv f t ≤ C) :
    f b ≤ C*(b-a) := by
  by_contra h
  have hstrict : C*(b-a) < f b := lt_of_not_ge h
  obtain ⟨y,hylo,hyhi⟩ := exists_between hstrict
  have hy0 : 0 < y := lt_of_le_of_lt (mul_nonneg hC (sub_nonneg.mpr hab)) hylo
  have hyB : y < B := hyhi.trans_le hB
  obtain ⟨t,ht,hty⟩ := intermediate_value_Icc hab hf ⟨by rw [hfa]; exact hy0.le,hyhi.le⟩
  let L : Set ℝ := Icc a b ∩ f ⁻¹' {y}
  have hLclosed : IsClosed L := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hLcompact : IsCompact L := isCompact_Icc.of_isClosed_subset hLclosed inter_subset_left
  obtain ⟨z,hz,hmin⟩ := hLcompact.exists_isMinOn ⟨t,ht,hty⟩ continuousOn_id
  have haz : a ≤ z := hz.1.1
  have hzb : z ≤ b := hz.1.2
  have hfz : f z = y := hz.2
  have hclosed : IsClosed (Icc a z ∩ f ⁻¹' {0}) :=
    (hf.mono (Icc_subset_Icc_right hzb)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact (Icc a z ∩ f ⁻¹' {0}) :=
    isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨x,hx,hmax⟩ := hcompact.exists_isMaxOn ⟨a,⟨le_rfl,haz⟩,hfa⟩ continuousOn_id
  have hax : a ≤ x := hx.1.1
  have hxz : x ≤ z := hx.1.2
  have hfx : f x = 0 := hx.2
  have hreg (r : ℝ) (hr : r ∈ Ioo x z) : r ∈ Ioo a b ∧ 0 < f r ∧ f r < B := by
    have hra : a < r := hax.trans_lt hr.1
    have hrb : r < b := hr.2.trans_le hzb
    have hfr : 0 < f r := by
      apply lt_of_le_of_ne (hpos r ⟨hra.le,hrb.le⟩)
      intro heq
      have hh : r ≤ x := hmax ⟨⟨hra.le,hr.2.le⟩,heq.symm⟩
      exact (not_le_of_gt hr.1) hh
    have hfry : f r < y := by
      by_contra hn
      obtain ⟨k,hk,hky⟩ := intermediate_value_Icc hra.le
        (hf.mono (Icc_subset_Icc_right hrb.le)) ⟨by rw [hfa]; exact hy0.le,le_of_not_gt hn⟩
      have hzk : z ≤ k := hmin ⟨⟨hk.1,hk.2.trans hrb.le⟩,hky⟩
      exact (not_le_of_gt hr.2) (hzk.trans hk.2)
    exact ⟨⟨hra,hrb⟩,hfr,hfry.trans hyB⟩
  have hbound := image_sub_le_mul_sub_of_deriv_le_off_finite E hxz
    (hf.mono (Icc_subset_Icc hax hzb))
    (fun r hr he => hd r (hreg r hr).1 he (hreg r hr).2.1 (hreg r hr).2.2)
    (fun r hr he => hb r (hreg r hr).1 he (hreg r hr).2.1 (hreg r hr).2.2)
  rw [hfz,hfx,sub_zero] at hbound
  have hlength : C*(z-x) ≤ C*(b-a) := mul_le_mul_of_nonneg_left (by linarith) hC
  exact (not_le_of_gt hylo) (hbound.trans hlength)

end PositiveEinsteinFour.Geometry

end OAI
