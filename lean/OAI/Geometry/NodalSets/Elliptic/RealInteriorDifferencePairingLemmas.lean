import OAI.Geometry.NodalSets.Elliptic.RealL2ZeroExtension
import OAI.Geometry.NodalSets.Elliptic.RealSmoothDifferenceLimit

namespace OAI

noncomputable section

namespace Yau

open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology

theorem real_interior_difference_pairing (u psi : Jets.Coord → ℝ)
    (hu : MemLp u 2 (volume.restrict (realFinCube 4)))
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube 4 (1/2))
    (i : Fin 4) (h : ℝ) (hh : |h| ≤ 1/8) :
    (∫ x in realCenteredCube 4 (1/2), realDifferenceQuotient i h u x*psi x) =
      -(∫ x in realFinCube 4, u x*realDifferenceQuotient i (-h) psi x) := by
  let U := (realFinCube 4).indicator u
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict (realCenteredCube_isCompact 4 1).measurableSet).mpr hu
  have hpsi := real_compact_continuous_memLp psi hp.continuous hc
  have heq := (real_differenceQuotient_pairing i h U psi hU hpsi).2.2
  have hz (x : Jets.Coord) (hx : x ∉ realCenteredCube 4 (1/2)) : psi x=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht))
  have hleft : (∫ x, realDifferenceQuotient i h U x*psi x) =
      ∫ x in realCenteredCube 4 (1/2), realDifferenceQuotient i h u x*psi x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := realCenteredCube 4 (1/2))
      (fun x hx ↦ by rw [hz x hx,mul_zero])]
    apply setIntegral_congr_fun (realCenteredCube_isCompact 4 (1/2)).measurableSet
    intro x hx
    have hx0 : x ∈ realFinCube 4 := realCenteredCube_mono (by norm_num) hx
    have hxt : x+Pi.single i h ∈ realFinCube 4 := by
      apply realCenteredCube_shift i (h := -h) (r := 1/2)
        (by simpa only [abs_neg] using (show |h| ≤ (1:ℝ)-1/2 by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    simp only [realDifferenceQuotient,U,indicator_of_mem hx0,indicator_of_mem hxt]
  have hright : (∫ x, U x*realDifferenceQuotient i (-h) psi x) =
      ∫ x in realFinCube 4, u x*realDifferenceQuotient i (-h) psi x := by
    change (∫ x, ((realFinCube 4).indicator u) x*realDifferenceQuotient i (-h) psi x) = _
    simp only [← Set.indicator_mul_left]
    exact integral_indicator (show MeasurableSet (realFinCube 4) from
      (realCenteredCube_isCompact 4 1).measurableSet)
  rw [hleft,hright] at heq
  exact heq

theorem real_interior_difference_pairing_tendsto (u psi : Jets.Coord → ℝ)
    (hu : MemLp u 2 (volume.restrict (realFinCube 4)))
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube 4 (1/2))
    (i : Fin 4) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1/8)
    (hlim : Tendsto (fun k ↦ -h k) atTop (𝓝[≠] (0:ℝ))) :
    Tendsto (fun k ↦ ∫ x in realCenteredCube 4 (1/2), realDifferenceQuotient i (h k) u x*psi x) atTop
      (𝓝 (-(∫ x in realCenteredCube 4 (1/2), u x*coordPartial psi x i))) := by
  let : IsFiniteMeasure (volume.restrict (realFinCube 4)) :=
    isFiniteMeasure_restrict.mpr (realCenteredCube_isCompact 4 1).measure_ne_top
  have hI : Integrable u (volume.restrict (realFinCube 4)) := hu.integrable (by norm_num)
  have ht := (real_smooth_difference_integral_tendsto (volume.restrict (realFinCube 4))
    u psi hI hp hc i (fun k ↦ -h k) hlim).neg
  have hd : tsupport (fun x ↦ coordPartial psi x i) ⊆ realCenteredCube 4 (1/2) :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hz (x : Jets.Coord) (hx : x ∉ realCenteredCube 4 (1/2)) : u x*coordPartial psi x i=0 := by
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y i)
      (fun ht ↦ hx (hd ht)),mul_zero]
  have hsame : (∫ x in realFinCube 4, u x*coordPartial psi x i) =
      ∫ x in realCenteredCube 4 (1/2), u x*coordPartial psi x i := by
    have hlarge : (∫ x in realFinCube 4, u x*coordPartial psi x i) =
        ∫ x, u x*coordPartial psi x i :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hz x
        (fun hm ↦ hx (realCenteredCube_mono (by norm_num) hm)))
    have hsmall : (∫ x in realCenteredCube 4 (1/2), u x*coordPartial psi x i) =
        ∫ x, u x*coordPartial psi x i := setIntegral_eq_integral_of_forall_compl_eq_zero hz
    exact hlarge.trans hsmall.symm
  rw [hsame] at ht
  convert ht using 1
  funext k
  exact real_interior_difference_pairing u psi hu hp hc hs i (h k) (hh k)

theorem real_nested_difference_pairing (R r e : ℝ) (hr : r ≤ R) (he : e ≤ R-r) (u psi : Jets.Coord → ℝ)
    (hu : MemLp u 2 (volume.restrict (realCenteredCube 4 R)))
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube 4 r)
    (i : Fin 4) (h : ℝ) (hh : |h| ≤ e) :
    (∫ x in realCenteredCube 4 r, realDifferenceQuotient i h u x*psi x) =
      -(∫ x in realCenteredCube 4 R, u x*realDifferenceQuotient i (-h) psi x) := by
  let U := (realCenteredCube 4 R).indicator u
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict (realCenteredCube_isCompact 4 R).measurableSet).mpr hu
  have hpsi := real_compact_continuous_memLp psi hp.continuous hc
  have heq := (real_differenceQuotient_pairing i h U psi hU hpsi).2.2
  have hz (x : Jets.Coord) (hx : x ∉ realCenteredCube 4 r) : psi x=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht))
  have hleft : (∫ x, realDifferenceQuotient i h U x*psi x) =
      ∫ x in realCenteredCube 4 r, realDifferenceQuotient i h u x*psi x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := realCenteredCube 4 r)
      (fun x hx ↦ by rw [hz x hx,mul_zero])]
    apply setIntegral_congr_fun (realCenteredCube_isCompact 4 r).measurableSet
    intro x hx
    have hx0 : x ∈ realCenteredCube 4 R := realCenteredCube_mono hr hx
    have hxt : x+Pi.single i h ∈ realCenteredCube 4 R := by
      apply realCenteredCube_shift i (h := -h) (r := r)
        (by simpa only [abs_neg] using (show |h| ≤ R-r by linarith))
      simpa only [Pi.single_neg,add_neg_cancel_right] using hx
    simp only [realDifferenceQuotient,U,indicator_of_mem hx0,indicator_of_mem hxt]
  have hright : (∫ x, U x*realDifferenceQuotient i (-h) psi x) =
      ∫ x in realCenteredCube 4 R, u x*realDifferenceQuotient i (-h) psi x := by
    change (∫ x, ((realCenteredCube 4 R).indicator u) x*realDifferenceQuotient i (-h) psi x) = _
    simp only [← Set.indicator_mul_left]
    exact integral_indicator (show MeasurableSet (realCenteredCube 4 R) from
      (realCenteredCube_isCompact 4 R).measurableSet)
  rw [hleft,hright] at heq
  exact heq

theorem real_nested_difference_pairing_tendsto (R r e : ℝ) (hr : r ≤ R) (he : e ≤ R-r) (u psi : Jets.Coord → ℝ)
    (hu : MemLp u 2 (volume.restrict (realCenteredCube 4 R)))
    (hp : ContDiff ℝ ∞ psi) (hc : HasCompactSupport psi)
    (hs : tsupport psi ⊆ realCenteredCube 4 r)
    (i : Fin 4) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ e)
    (hlim : Tendsto (fun k ↦ -h k) atTop (𝓝[≠] (0:ℝ))) :
    Tendsto (fun k ↦ ∫ x in realCenteredCube 4 r, realDifferenceQuotient i (h k) u x*psi x) atTop
      (𝓝 (-(∫ x in realCenteredCube 4 r, u x*coordPartial psi x i))) := by
  let : IsFiniteMeasure (volume.restrict (realCenteredCube 4 R)) :=
    isFiniteMeasure_restrict.mpr (realCenteredCube_isCompact 4 R).measure_ne_top
  have hI : Integrable u (volume.restrict (realCenteredCube 4 R)) := hu.integrable (by norm_num)
  have ht := (real_smooth_difference_integral_tendsto (volume.restrict (realCenteredCube 4 R))
    u psi hI hp hc i (fun k ↦ -h k) hlim).neg
  have hd : tsupport (fun x ↦ coordPartial psi x i) ⊆ realCenteredCube 4 r :=
    (tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hs
  have hz (x : Jets.Coord) (hx : x ∉ realCenteredCube 4 r) : u x*coordPartial psi x i=0 := by
    rw [image_eq_zero_of_notMem_tsupport (f := fun y ↦ coordPartial psi y i)
      (fun ht ↦ hx (hd ht)),mul_zero]
  have hsame : (∫ x in realCenteredCube 4 R, u x*coordPartial psi x i) =
      ∫ x in realCenteredCube 4 r, u x*coordPartial psi x i := by
    have hlarge : (∫ x in realCenteredCube 4 R, u x*coordPartial psi x i) =
        ∫ x, u x*coordPartial psi x i :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ hz x
        (fun hm ↦ hx (realCenteredCube_mono hr hm)))
    have hsmall : (∫ x in realCenteredCube 4 r, u x*coordPartial psi x i) =
        ∫ x, u x*coordPartial psi x i := setIntegral_eq_integral_of_forall_compl_eq_zero hz
    exact hlarge.trans hsmall.symm
  rw [hsame] at ht
  convert ht using 1
  funext k
  exact real_nested_difference_pairing R r e hr he u psi hu hp hc hs i (h k) (hh k)

end Yau

end

end OAI
