import OAI.Analysis.KadisonKastler.BilateralL2Transport

namespace OAI

/-! Composition and inverse identities for the bilateral L2 shifts. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {G K : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K]

theorem bilateralTranslateL2_zero (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 0 f = f := by
  apply Lp.ext
  have h := bilateralTranslateL2_ae 0 f
  have hzero : bilateralTranslate G 0 = id := by funext ω j; simp [bilateralTranslate]
  simpa only [hzero, Function.comp_id] using h

theorem bilateralTranslateL2_add (a b : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 a (bilateralTranslateL2 b f) = bilateralTranslateL2 (a + b) f := by
  apply Lp.ext
  have hb := (bilateralTranslate_measurePreserving G a).quasiMeasurePreserving.ae
    (bilateralTranslateL2_ae b f)
  filter_upwards [bilateralTranslateL2_ae a (bilateralTranslateL2 b f), hb,
    bilateralTranslateL2_ae (a + b) f] with ω h₁ h₂ h₃
  dsimp only [Function.comp_apply] at h₁ h₂ h₃
  rw [h₁, h₂, h₃, bilateralTranslate_add, add_comm b a]

theorem bilateralTranslateL2_inverse (a : ℤ) (f : Lp K 2 (bilateralWalkLaw G)) :
    bilateralTranslateL2 a (bilateralTranslateL2 (-a) f) = f := by
  rw [bilateralTranslateL2_add, add_neg_cancel, bilateralTranslateL2_zero]

end

end KadisonKastler

end OAI
