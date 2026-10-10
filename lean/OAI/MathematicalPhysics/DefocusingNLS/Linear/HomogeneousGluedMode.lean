import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedCanonicalTail
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedLocalL2
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedCutoff
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGluedEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpectralMode

namespace OAI

/-! Canonical outgoing states yield bounded radial modes in Re lambda >= -a. -/

open Set Filter MeasureTheory Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "V" => ℂ × ℂ
local notation "E₄" => V × V

theorem homogeneousGlued_canonical_mode
    (a b : ℝ) (ell m N : ℕ) (hN : 7 ≤ N) (ν beta lam : ℂ)
    (hν : ν = -2 * (a : ℂ) + 2 * Complex.I * (b : ℂ))
    (hhalf : -a ≤ lam.re) (L : ℝ) (hX : HasRadialExterior ν m beta L)
    (Q : ℝ → ℂ) (hQ : ContDiff ℝ ∞ Q) (U : ℝ → E₄)
    (hc : ContDiff ℝ 2 (fun r => (U r).1.1) ∧
      ContDiff ℝ 2 (fun r => (U r).2.1))
    (hU : ∀ r, 0 < r → HasDerivAt U
      (spectralPhysicalCircularField (ν - 2 * lam) (star ν - 2 * lam)
        ((ell * (ell + 10) : ℕ) : ℂ) m (Q r) r (U r)) r)
    (R : ℝ) (hR : 0 < R) (hne : U R ≠ 0)
    (Yp Ym : ℂ → ℝ → E₄)
    (hp : IsCanonicalHolomorphicColumn ν ((ell * (ell + 10) : ℕ) : ℂ) beta m L (1, 0) Yp)
    (hm : IsCanonicalHolomorphicColumn ν ((ell * (ell + 10) : ℕ) : ℂ) beta m L (0, 1) Ym)
    (c d : ℂ) (ho : ∀ r, R ≤ r → U r =
      c • spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Yp lam) r +
        d • spectralPhysicalPair (ν - 2 * lam) (star ν - 2 * lam) (Ym lam) r) :
    Nonempty (RadialSpectralMode a b m N Q ((ell * (ell + 10) : ℕ) : ℂ) lam) := by
  let f := fun r => (U r).1.1
  let g := fun r => (U r).2.1
  let F := fun r => (f r, g r)
  have hsU := homogeneousGlued_state_smooth (ν - 2 * lam) (star ν - 2 * lam)
    ((ell * (ell + 10) : ℕ) : ℂ) m Q hQ.contDiffOn U hU
  have hfs : ContDiffOn ℝ ∞ f (Ioi 0) := hsU.fst.fst
  have hgs : ContDiffOn ℝ ∞ g (Ioi 0) := hsU.snd.fst
  have hFs : ContDiffOn ℝ ∞ F (Ioi 0) := hfs.prodMk hgs
  have horigin (T : ℝ) (hT : 0 < T) := homogeneousGlued_origin_regularity ell m
    (ν - 2 * lam) (star ν - 2 * lam) T hT Q hQ.continuous hQ.contDiffOn U hc
    (fun r hr => hU r hr.1)
  let σ := (ν - 2 * lam).re
  have hνre : ν.re = -2 * a := by
    rw [hν]
    simp [Complex.mul_re, Complex.mul_im]
  have hσ : σ ≤ 0 := by
    have he : σ = -2 * a - 2 * lam.re := by
      dsimp only [σ]
      rw [Complex.sub_re, hνre]
      norm_num [Complex.mul_re]
    rw [he]
    linarith
  have htail (j : ℕ) := homogeneousGlued_canonical_tail_bound ν
    ((ell * (ell + 10) : ℕ) : ℂ) beta m L hX lam Yp Ym hp hm U hsU R hR c d ho j
  have hscalar (j : ℕ) :
      (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop, ‖iteratedDeriv j f r‖ ≤ C * r ^ (σ - j)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in atTop, ‖iteratedDeriv j g r‖ ≤ C * r ^ (σ - j)) := by
    obtain ⟨C, hC, hb⟩ := htail j
    constructor
    · refine ⟨C, hC, ?_⟩
      filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
      exact (homogeneousGlued_coordinate_derivatives F hFs j r hr0).1.trans hr
    · refine ⟨C, hC, ?_⟩
      filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
      exact (homogeneousGlued_coordinate_derivatives F hFs j r hr0).2.trans hr
  have hexp : 11 + 2 * (σ - (N : ℝ)) < -1 := by
    have hN' : (7 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hft := homogeneousGlued_top_integrable f N (σ - N)
    (fun T hT => (horigin T hT).1) hfs hexp (hscalar N).1
  have hgt := homogeneousGlued_top_integrable g N (σ - N)
    (fun T hT => (horigin T hT).2) hgs hexp (hscalar N).2
  have hbF : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ r in atTop, ‖F r‖ ≤ M := by
    obtain ⟨C, hC, hb⟩ := htail 0
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with r hr hr1
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hr
    exact hr.trans (mul_le_of_le_one_right hC
      (Real.rpow_le_one_of_one_le_of_nonpos hr1 hσ))
  obtain ⟨Mf, hMf, hbf⟩ := homogeneousGluedCutoff_bounded f hc.1.continuous
    (by obtain ⟨M, hM, hb⟩ := hbF; exact ⟨M, hM, hb.mono (fun r hr => (norm_fst_le (F r)).trans hr)⟩)
  obtain ⟨Mg, hMg, hbg⟩ := homogeneousGluedCutoff_bounded g hc.2.continuous
    (by obtain ⟨M, hM, hb⟩ := hbF; exact ⟨M, hM, hb.mono (fun r hr => (norm_snd_le (F r)).trans hr)⟩)
  have heq : IsHarmonicRadialEigenpair a b m Q ((ell * (ell + 10) : ℕ) : ℂ) lam f g := by
    have hstar : star ν = -2 * (a : ℂ) - 2 * Complex.I * (b : ℂ) := by
      rw [hν]
      simp only [star_add, star_mul, star_neg, star_ofNat, Complex.star_def,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    have hh := homogeneousGlued_eigenpair a b ((ell * (ell + 10) : ℕ) : ℝ) lam m Q U
      (by simpa only [← hν, ← hstar, Complex.ofReal_natCast] using hU)
    simpa only [Complex.ofReal_natCast] using hh
  refine ⟨⟨homogeneousGluedCutoff f, homogeneousGluedCutoff g,
    homogeneousGluedCutoff_contDiff f hc.1, homogeneousGluedCutoff_contDiff g hc.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    have hf := homogeneousGluedCutoff_eventuallyEq f r hr
    have hg := homogeneousGluedCutoff_eventuallyEq g r hr
    simpa only [← hf.eq_of_nhds, ← hg.eq_of_nhds, ← hf.deriv_eq, ← hg.deriv_eq,
      ← hf.deriv.deriv_eq, ← hg.deriv.deriv_eq] using heq r hr
  · exact ((Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).contDiffOn.mul hfs)
  · exact ((Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).contDiffOn.mul hgs)
  · apply hft.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [homogeneousGluedCutoff_iteratedDeriv f N r hr]
  · apply hgt.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only
    rw [homogeneousGluedCutoff_iteratedDeriv g N r hr]
  · exact ⟨max Mf Mg, hMf.trans (le_max_left _ _), fun r =>
      max_le ((hbf r).trans (le_max_left _ _)) ((hbg r).trans (le_max_right _ _))⟩
  · obtain ⟨r, hr, hn⟩ := homogeneousGlued_nonzero_values
      (ν - 2 * lam) (star ν - 2 * lam) ((ell * (ell + 10) : ℕ) : ℂ) m Q U R hR hne hU
    refine ⟨r, hr, ?_⟩
    simpa only [homogeneousGluedCutoff_eq f r hr.le,
      homogeneousGluedCutoff_eq g r hr.le] using hn

end DefocusingNLS

end OAI
