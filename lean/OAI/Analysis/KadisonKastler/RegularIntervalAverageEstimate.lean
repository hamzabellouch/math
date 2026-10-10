import OAI.Analysis.KadisonKastler.RegularIntervalCutoffs

namespace OAI

/-! # The boundary estimate for interval localization

An integrable coefficient which equals its invariant value on the
interior interval and vanishes beyond the enlarged interval has an
error controlled by the fixed-width boundary strip.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

theorem regular_interval_boundary_estimate
    {A R C : ℝ} (hA : 0 ≤ A) (hR : A ≤ R) (hC : 0 ≤ C)
    (F : ℝ → ℂ) (hF : Integrable F volume) (c : ℂ)
    (hc : ‖c‖ ≤ C) (hb : ∀ r, ‖F r‖ ≤ C)
    (hinner : ∀ r, |r| + A ≤ R → F r = c)
    (houter : ∀ r, R + A < |r| → F r = 0) :
    ‖(∫ r : ℝ, F r) - (2 * R : ℝ) • c‖ ≤ 8 * A * C := by
  let I : Set ℝ := Set.Icc (-R + A) (R - A)
  let J : Set ℝ := Set.Icc (-R - A) (R + A)
  let B : Set ℝ := Set.Icc (-R) R
  let D : Set ℝ := J \ I
  have hRI : -R + A ≤ R - A := by linarith
  have hRJ : -R - A ≤ R + A := by linarith
  have hRB : -R ≤ R := by linarith
  have hIJ : I ⊆ J := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hIB : I ⊆ B := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hBJ : B ⊆ J := by
    intro r hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hJfin : volume J ≠ ⊤ := by simp [J, Real.volume_Icc]
  have hBfin : volume B ≠ ⊤ := by simp [B, Real.volume_Icc]
  have hDfin : volume D < ⊤ := lt_top_iff_ne_top.mpr
    (measure_ne_top_of_subset Set.sdiff_subset hJfin)
  have hDmeas : MeasurableSet D := measurableSet_Icc.diff measurableSet_Icc
  have hDmass : (volume D).toReal = 4 * A := by
    change volume.real (J \ I) = _
    rw [measureReal_sdiff hIJ measurableSet_Icc hJfin]
    simp only [I, J, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal
      (sub_nonneg.mpr hRI), ENNReal.toReal_ofReal (sub_nonneg.mpr hRJ)]
    ring
  have hBmass : (volume B).toReal = 2 * R := by
    simp only [B, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hRB)]
    ring
  let E : ℝ → ℂ := fun r => F r - B.indicator (fun _ => c) r
  have hzero : ∀ r, r ∉ D → E r = 0 := by
    intro r hr
    by_cases hrI : r ∈ I
    · have habs : |r| + A ≤ R := by
        have ha : |r| ≤ R - A := abs_le.mpr
          ⟨by linarith [hrI.1], by linarith [hrI.2]⟩
        linarith
      simp only [E, hinner r habs, Set.indicator_of_mem (hIB hrI), sub_self]
    · have hrJ : r ∉ J := fun hj => hr ⟨hj, hrI⟩
      have habs : R + A < |r| := by
        by_contra hh
        have hh' := le_of_not_gt hh
        have he := abs_le.mp hh'
        exact hrJ ⟨by linarith [he.1], he.2⟩
      simp only [E, houter r habs, Set.indicator_of_notMem (fun hb => hrJ (hBJ hb)), sub_self]
  have hE : E = D.indicator E := by
    funext r
    by_cases hr : r ∈ D
    · exact (Set.indicator_of_mem hr E).symm
    · rw [Set.indicator_of_notMem hr, hzero r hr]
  have hbound : ∀ r, ‖E r‖ ≤ 2 * C := by
    intro r
    apply (norm_sub_le _ _).trans
    have hb' : ‖B.indicator (fun _ => c) r‖ ≤ C := by
      by_cases hr : r ∈ B
      · simpa only [Set.indicator_of_mem hr] using hc
      · simpa only [Set.indicator_of_notMem hr, norm_zero] using hC
    linarith [hb r, hb']
  have hnorm : ‖∫ r : ℝ, E r‖ ≤ 8 * A * C := by
    conv_lhs => rw [hE, integral_indicator hDmeas]
    have he := norm_setIntegral_le_of_norm_le_const_ae' hDfin
      (Eventually.of_forall fun r (_ : r ∈ D) => hbound r)
    change ‖∫ r in D, E r‖ ≤ _ at he
    rw [measureReal_def, hDmass] at he
    convert he using 1; ring
  have hconst : Integrable (B.indicator fun _ => c) volume := by
    exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hBfin)
  have hIntegral : (∫ r : ℝ, E r) = (∫ r : ℝ, F r) - (2 * R : ℝ) • c := by
    rw [integral_sub hF hconst, integral_indicator measurableSet_Icc, integral_const]
    rw [measureReal_def, Measure.restrict_apply_univ]
    rw [hBmass]
  rwa [hIntegral] at hnorm

end

end KadisonKastler

end OAI
