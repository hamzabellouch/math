import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace OAI

/-! # The future minimum of a scale profile on the unit interval -/

namespace Falconer
open Set
open scoped NNReal

noncomputable def profileSuffixMinimum (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf (f '' Icc u 1)

theorem profileSuffixMinimum_attained {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {u : ℝ} (hu : u ∈ Icc 0 1) :
    ∃ v ∈ Icc u 1, profileSuffixMinimum f u = f v ∧
      ∀ w ∈ Icc u 1, f v ≤ f w := by
  obtain ⟨v,hv,hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hu.2)
    (hf.mono (Icc_subset_Icc hu.1 le_rfl))
  refine ⟨v,hv,?_,hm⟩
  exact (show IsLeast (f '' Icc u 1) (f v) from
    ⟨mem_image_of_mem f hv,by rintro _ ⟨w,hw,rfl⟩; exact hm hw⟩).csInf_eq

theorem profileSuffixMinimum_le {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) {u w : ℝ} (hu : u ∈ Icc 0 1)
    (hw : w ∈ Icc u 1) : profileSuffixMinimum f u ≤ f w := by
  obtain ⟨v,_,he,hm⟩ := profileSuffixMinimum_attained hf hu
  rw [he]
  exact hm w hw

theorem profileSuffixMinimum_monotone {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) : MonotoneOn (profileSuffixMinimum f) (Icc 0 1) := by
  intro u hu v hv huv
  obtain ⟨w,hw,he,_⟩ := profileSuffixMinimum_attained hf hv
  rw [he]
  exact profileSuffixMinimum_le hf hu ⟨huv.trans hw.1,hw.2⟩

theorem profileSuffixMinimum_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 1)) :
    LipschitzOnWith K (profileSuffixMinimum f) (Icc 0 1) := by
  have hc := hf.continuousOn
  have hmono := profileSuffixMinimum_monotone hc
  have hstep {u v : ℝ} (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) (huv : u ≤ v) :
      profileSuffixMinimum f v-profileSuffixMinimum f u ≤ K*(v-u) := by
    obtain ⟨w,hw,he,hm⟩ := profileSuffixMinimum_attained hc hu
    by_cases hwv : v ≤ w
    · have hle := profileSuffixMinimum_le hc hv ⟨hwv,hw.2⟩
      rw [he]
      nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr huv)]
    · have hwv' : w ≤ v := (lt_of_not_ge hwv).le
      have hle := profileSuffixMinimum_le hc hv ⟨le_rfl,hv.2⟩
      have hd := hf.dist_le_mul w ⟨hu.1.trans hw.1,hw.2⟩ v hv
      rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hwv')] at hd
      have hfv : f v-f w ≤ K*(v-w) := by
        linarith [le_abs_self (f w-f v),neg_le_abs (f w-f v)]
      rw [he]
      nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr hw.1)]
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hmono hu hv huv)),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hstep hu hv huv
  · rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmono hv hu hvu)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hstep hv hu hvu

end Falconer

end OAI
