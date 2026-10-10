import OAI.InformationTheory.BooleanNoise.Basic
import OAI.InformationTheory.BooleanNoise.InverseScalars
import OAI.InformationTheory.BooleanNoise.InverseRegularity
import OAI.InformationTheory.BooleanNoise.CurvatureBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

namespace OAI

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem hasDerivAt_tangent_extension (F : ℝ → ℝ) {c d : ℝ}
    (hF : HasDerivAt F d c) :
    HasDerivAt (fun s => if s ≤ c then F s else F c + d * (s - c)) d c := by
  let T : ℝ → ℝ := fun s => if s ≤ c then F s else F c + d * (s - c)
  have hleft : HasDerivWithinAt T d (Iic c) c := by
    apply hF.hasDerivWithinAt.congr
    · intro s hs
      change s ≤ c at hs
      simp only [T, ite_eq_left hs]
    · simp [T]
  have hline : HasDerivAt (fun s : ℝ => F c + d * (s - c)) d c := by
    convert! (((hasDerivAt_id c).sub_const c).const_mul d).const_add (F c) using 1
    ring
  have hright : HasDerivWithinAt T d (Ici c) c := by
    apply hline.hasDerivWithinAt.congr
    · intro s hs
      change c ≤ s at hs
      rcases hs.eq_or_lt with rfl | hs
      · simp [T]
      · simp [T, not_le.mpr hs]
    · simp [T]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

theorem clamp_nonexpansive (c x y : ℝ) :
    |min (max x 0) c - min (max y 0) c| ≤ |x - y| := by
  have h : LipschitzWith 1 (fun s : ℝ => min (max s 0) c) :=
    (LipschitzWith.id.max_const 0).min_const c
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

theorem K_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : K s = 0 := by simp [K, hs]

theorem KDeriv_eq_clamp (s : ℝ) :
    KDeriv s = rDeriv (min (max s 0) s0) - 2 := by
  by_cases hs : s ≤ 0
  · simp [KDeriv, hs, min_eq_left s0_pos.le]
  · have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
    by_cases hsc : s ≤ s0
    · simp [KDeriv, hs, hsc, max_eq_left hs0]
    · simp [KDeriv, hs, hsc, max_eq_left hs0, min_eq_right (le_of_not_ge hsc)]

theorem K_eq_rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsc : s ≤ s0) : K s = rGap s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · exact K_eq_rGap hs hsc

theorem clamp_mem_inverse_domain (s : ℝ) : min (max s 0) s0 ∈ Ico 0 ell :=
  ⟨le_min (le_max_right s 0) s0_pos.le, (min_le_right _ _).trans_lt s0_lt_ell⟩

theorem hasDerivAt_K_pos {s : ℝ} (hs : 0 < s) : HasDerivAt K (KDeriv s) s := by
  by_cases hsc : s < s0
  · have he : K =ᶠ[𝓝 s] rGap := by
      filter_upwards [Ioo_mem_nhds hs hsc] with t ht
      exact K_eq_rGap ht.1 ht.2.le
    have hKd : KDeriv s = rDeriv s - 2 := by simp [KDeriv, not_le.mpr hs, hsc.le]
    rw [hKd]
    exact (hasDerivAt_rGap ⟨hs, hsc.trans s0_lt_ell⟩).congr_of_eventuallyEq he
  · have hsc' : s0 ≤ s := le_of_not_gt hsc
    rcases hsc'.eq_or_lt with rfl | hsc'
    · have hjoin := hasDerivAt_tangent_extension rGap (hasDerivAt_rGap ⟨s0_pos, s0_lt_ell⟩)
      have he : K =ᶠ[𝓝 s0]
          (fun t => if t ≤ s0 then rGap t else rGap s0 + (rDeriv s0 - 2) * (t - s0)) := by
        filter_upwards [Ioi_mem_nhds s0_pos] with t ht
        change 0 < t at ht
        simp only [K, ite_eq_right (not_le.mpr ht)]
      have hKd : KDeriv s0 = rDeriv s0 - 2 := by simp [KDeriv, not_le.mpr s0_pos]
      rw [hKd]
      exact hjoin.congr_of_eventuallyEq he
    · have hline : HasDerivAt
          (fun t : ℝ => rGap s0 + (rDeriv s0 - 2) * (t - s0)) (rDeriv s0 - 2) s := by
        convert! (((hasDerivAt_id s).sub_const s0).const_mul (rDeriv s0 - 2)).const_add
          (rGap s0) using 1
        ring
      have he : K =ᶠ[𝓝 s]
          (fun t => rGap s0 + (rDeriv s0 - 2) * (t - s0)) := by
        filter_upwards [Ioi_mem_nhds hsc'] with t ht
        exact K_eq_tangent (s0_pos.trans ht) ht.le
      have hKd : KDeriv s = rDeriv s0 - 2 := by
        simp [KDeriv, not_le.mpr hs, not_le.mpr hsc']
      rw [hKd]
      exact hline.congr_of_eventuallyEq he

theorem hasDerivAt_K_zero_of_right_derivative
    (hzero : HasDerivWithinAt rGap 0 (Ici 0) 0) : HasDerivAt K 0 0 := by
  have hleft : HasDerivWithinAt K 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro s hs
      exact K_eq_zero_of_nonpos hs
    · simp
  have hright : HasDerivWithinAt K 0 (Ici 0) 0 := by
    apply hzero.congr_of_eventuallyEq
    · have hnear : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, s < s0 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds s0_pos)
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs hs0
      exact K_eq_rGap_nonneg hs hs0.le
    · simp
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

theorem KDeriv_monotone_of_rDeriv
    (hmono : MonotoneOn rDeriv (Ico 0 ell)) : Monotone KDeriv := by
  intro x y hxy
  rw [KDeriv_eq_clamp, KDeriv_eq_clamp]
  exact sub_le_sub_right
    (hmono (clamp_mem_inverse_domain x) (clamp_mem_inverse_domain y)
      (min_le_min_right s0 (max_le_max_right 0 hxy))) 2

theorem KDeriv_lipschitz_of_rDeriv {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc (0 : ℝ) s0, ∀ y ∈ Icc (0 : ℝ) s0,
      |rDeriv x - rDeriv y| ≤ C * |x - y|) (x y : ℝ) :
    |KDeriv x - KDeriv y| ≤ C * |x - y| := by
  rw [KDeriv_eq_clamp, KDeriv_eq_clamp]
  have hx : min (max x 0) s0 ∈ Icc (0 : ℝ) s0 :=
    ⟨le_min (le_max_right x 0) s0_pos.le, min_le_right _ _⟩
  have hy : min (max y 0) s0 ∈ Icc (0 : ℝ) s0 :=
    ⟨le_min (le_max_right y 0) s0_pos.le, min_le_right _ _⟩
  rw [show rDeriv (min (max x 0) s0) - 2 - (rDeriv (min (max y 0) s0) - 2) =
    rDeriv (min (max x 0) s0) - rDeriv (min (max y 0) s0) by ring]
  exact (hbound _ hx _ hy).trans
    (mul_le_mul_of_nonneg_left (clamp_nonexpansive s0 x y) hC)

theorem rDeriv_increment_le_of_continuous
    (hcont : ContinuousOn rDeriv (Icc 0 s0))
    {x y : ℝ} (hx : x ∈ Icc 0 s0) (hy : y ∈ Icc 0 s0) (hxy : x ≤ y) :
    rDeriv y - rDeriv x ≤ (1 / ell) * (y - x) := by
  have hdiff : DifferentiableOn ℝ rDeriv (interior (Icc 0 s0)) := by
    intro s hs
    have hsi : s ∈ Ioo 0 s0 := by simpa only [interior_Icc] using hs
    exact (hasDerivAt_rDeriv ⟨hsi.1, hsi.2.trans s0_lt_ell⟩).differentiableAt.differentiableWithinAt
  have hbound : ∀ s ∈ interior (Icc 0 s0), deriv rDeriv s ≤ 1 / ell := by
    intro s hs
    have hsi : s ∈ Ioo 0 s0 := by simpa only [interior_Icc] using hs
    rw [(hasDerivAt_rDeriv ⟨hsi.1, hsi.2.trans s0_lt_ell⟩).deriv]
    exact rSecondDeriv_le_inv_ell hsi.1.le hsi.2.le
  exact (convex_Icc (0 : ℝ) s0).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hbound x hx y hy hxy

theorem rDeriv_lipschitz_of_continuous_monotone
    (hcont : ContinuousOn rDeriv (Icc 0 s0))
    (hmono : MonotoneOn rDeriv (Icc 0 s0))
    {x y : ℝ} (hx : x ∈ Icc 0 s0) (hy : y ∈ Icc 0 s0) :
    |rDeriv x - rDeriv y| ≤ (1 / ell) * |x - y| := by
  rcases le_total x y with hxy | hyx
  · calc
      |rDeriv x - rDeriv y| = rDeriv y - rDeriv x := by
        rw [abs_of_nonpos (sub_nonpos.mpr (hmono hx hy hxy))]
        ring
      _ ≤ (1 / ell) * (y - x) := rDeriv_increment_le_of_continuous hcont hx hy hxy
      _ = (1 / ell) * |x - y| := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hy hx hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact rDeriv_increment_le_of_continuous hcont hy hx hyx

theorem K_le_rGap_of_convex (hconvex : ConvexOn ℝ (Ico 0 ell) rGap)
    {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : K s ≤ rGap s := by
  by_cases hsc : s ≤ s0
  · rw [K_eq_rGap_nonneg hs hsc]
  · have hsc' : s0 < s := lt_of_not_ge hsc
    rw [K_eq_tangent (s0_pos.trans hsc') hsc'.le]
    have hslope := hconvex.le_slope_of_hasDerivAt ⟨s0_pos.le, s0_lt_ell⟩
      ⟨hs, hsell⟩ hsc' (hasDerivAt_rGap ⟨s0_pos, s0_lt_ell⟩)
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hsc')).mp hslope
    linarith

theorem K_nonneg_of_rGap_nonneg
    (hgap : ∀ s : ℝ, 0 ≤ s → s < ell → 0 ≤ rGap s)
    (hslope : 0 ≤ rDeriv s0 - 2) (s : ℝ) : 0 ≤ K s := by
  by_cases hs : s ≤ 0
  · rw [K_eq_zero_of_nonpos hs]
  · have hs' : 0 < s := lt_of_not_ge hs
    by_cases hsc : s ≤ s0
    · rw [K_eq_rGap hs' hsc]
      exact hgap s hs'.le (hsc.trans_lt s0_lt_ell)
    · have hsc' : s0 < s := lt_of_not_ge hsc
      rw [K_eq_tangent hs' hsc'.le]
      exact add_nonneg (hgap s0 s0_pos.le s0_lt_ell)
        (mul_nonneg hslope (sub_nonneg.mpr hsc'.le))

theorem convexOn_K_of_shape
    (hzero : HasDerivWithinAt rGap 0 (Ici 0) 0)
    (hmono : MonotoneOn rDeriv (Ico 0 ell)) : ConvexOn ℝ (Ici 0) K := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt K (KDeriv s) s := by
    intro s hs
    rcases (show 0 ≤ s from hs).eq_or_lt with rfl | hs
    · simpa only [KDeriv_zero] using hasDerivAt_K_zero_of_right_derivative hzero
    · exact hasDerivAt_K_pos hs
  have hc : ContinuousOn K (Ici 0) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ K (interior (Ici 0)) := by
    intro s hs
    exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hm : MonotoneOn (deriv K) (interior (Ici 0)) := by
    intro x hx y hy hxy
    rw [(hd x (interior_subset hx)).deriv, (hd y (interior_subset hy)).deriv]
    exact KDeriv_monotone_of_rDeriv hmono hxy
  exact hm.convexOn_of_deriv (convex_Ici 0) hc hdiff

theorem hasDerivAt_K {s : ℝ} (hs : 0 ≤ s) : HasDerivAt K (KDeriv s) s := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa only [KDeriv_zero] using
      hasDerivAt_K_zero_of_right_derivative hasDerivWithinAt_rGap_zero
  · exact hasDerivAt_K_pos hs

theorem continuousOn_K : ContinuousOn K (Ici 0) :=
  fun _s hs => (hasDerivAt_K hs).continuousAt.continuousWithinAt

theorem monotone_KDeriv : Monotone KDeriv :=
  KDeriv_monotone_of_rDeriv monotoneOn_rDeriv

theorem KDeriv_nonneg (s : ℝ) : 0 ≤ KDeriv s := by
  rw [KDeriv_eq_clamp]
  exact sub_nonneg.mpr (rDeriv_ge_two (clamp_mem_inverse_domain s).1
    (clamp_mem_inverse_domain s).2)

theorem monotoneOn_K : MonotoneOn K (Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := KDeriv)
    (convex_Ici 0) continuousOn_K ?_ ?_
  · intro s hs
    exact (hasDerivAt_K (interior_subset hs)).hasDerivWithinAt
  · intro s _
    exact KDeriv_nonneg s

theorem convexOn_K : ConvexOn ℝ (Ici 0) K :=
  convexOn_K_of_shape hasDerivWithinAt_rGap_zero monotoneOn_rDeriv

theorem K_nonneg (s : ℝ) : 0 ≤ K s :=
  K_nonneg_of_rGap_nonneg (fun _ hs hsell => rGap_nonneg hs hsell)
    (sub_nonneg.mpr (rDeriv_ge_two s0_pos.le s0_lt_ell)) s

theorem K_le_rGap {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : K s ≤ rGap s :=
  K_le_rGap_of_convex convexOn_rGap hs hsell

theorem KDeriv_lipschitz (x y : ℝ) :
    |KDeriv x - KDeriv y| ≤ (1 / ell) * |x - y| := by
  apply KDeriv_lipschitz_of_rDeriv (le_of_lt (one_div_pos.mpr ell_pos))
  intro a ha b hb
  have hsub : Icc (0 : ℝ) s0 ⊆ Ico 0 ell :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt s0_lt_ell⟩
  exact rDeriv_lipschitz_of_continuous_monotone
    (continuousOn_rDeriv.mono hsub) (monotoneOn_rDeriv.mono hsub) ha hb

end LeanBlast.CourtadeKumar

end OAI
