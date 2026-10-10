import OAI.Analysis.KadisonKastler.ResolventLocalizedMeasure
import OAI.Analysis.KadisonKastler.ResolventSqrtCalculus
import OAI.Analysis.KadisonKastler.RelativeSquareRootBound

namespace OAI

/-! # Relative root estimates from a localized vector measure -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventSqrt_local_error
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hpos : 0 ≤ R)
    (x : H) (l u : ℝ)
    (hlo : resolventLowerCut R l x = 0) (hhi : resolventLowerCut R u x = x)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε)
    (hb : ∀ s : spectrum ℝ R, l ≤ s.val → s.val < u → |s.val-t| ≤ ε*t) :
    ‖CFC.sqrt R x - (Real.sqrt t : ℂ) • x‖ ≤ ε * Real.sqrt t * ‖x‖ := by
  let f : C(spectrum ℝ R, ℂ) := resolventSqrtFunction R - ContinuousMap.const _ (Real.sqrt t : ℂ)
  have he : resolventContinuousCalculus R hR f x =
      CFC.sqrt R x-(Real.sqrt t : ℂ) • x := by
    simp only [f, map_sub, resolventContinuousCalculus_sqrt R hR hpos, sub_apply]
    congr 1
    have hc : ContinuousMap.const (spectrum ℝ R) (Real.sqrt t : ℂ) =
        (Real.sqrt t : ℂ) • (1 : C(spectrum ℝ R, ℂ)) := by ext; simp
    rw [hc, map_smul, map_one, smul_apply, one_apply_eq_self]
  rw [← he]
  apply resolventContinuousCalculus_local_bound R hR x l u hlo hhi f (by positivity)
  intro s hs hu
  change ‖((Real.sqrt s.val : ℂ) - (Real.sqrt t : ℂ))‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact relative_sqrt_sub_bound (spectrum_nonneg_of_nonneg hpos s.property) ht (hb s hs hu)

theorem resolventComplementSqrt_local_error
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hpos : 0 ≤ 1-R)
    (x : H) (l u : ℝ)
    (hlo : resolventLowerCut R l x = 0) (hhi : resolventLowerCut R u x = x)
    {t ε : ℝ} (ht : t < 1) (hε : 0 ≤ ε)
    (hspec : ∀ s : spectrum ℝ R, s.val ≤ 1)
    (hb : ∀ s : spectrum ℝ R, l ≤ s.val → s.val < u → |s.val-t| ≤ ε*(1-t)) :
    ‖CFC.sqrt (1-R) x - (Real.sqrt (1-t) : ℂ) • x‖ ≤ ε * Real.sqrt (1-t) * ‖x‖ := by
  let f : C(spectrum ℝ R, ℂ) :=
    resolventComplementSqrtFunction R - ContinuousMap.const _ (Real.sqrt (1-t) : ℂ)
  have he : resolventContinuousCalculus R hR f x =
      CFC.sqrt (1-R) x-(Real.sqrt (1-t) : ℂ) • x := by
    simp only [f, map_sub, resolventContinuousCalculus_complement_sqrt R hR hpos, sub_apply]
    congr 1
    have hc : ContinuousMap.const (spectrum ℝ R) (Real.sqrt (1-t) : ℂ) =
        (Real.sqrt (1-t) : ℂ) • (1 : C(spectrum ℝ R, ℂ)) := by ext; simp
    rw [hc, map_smul, map_one, smul_apply, one_apply_eq_self]
  rw [← he]
  apply resolventContinuousCalculus_local_bound R hR x l u hlo hhi f (by positivity)
  intro s hs hu
  change ‖((Real.sqrt (1-s.val) : ℂ) - (Real.sqrt (1-t) : ℂ))‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  apply relative_sqrt_sub_bound (sub_nonneg.mpr (hspec s)) (sub_pos.mpr ht)
  simpa only [show (1-s.val)-(1-t)= -(s.val-t) by ring, abs_neg] using hb s hs hu

end

end KadisonKastler

end OAI
