import OAI.Geometry.RCD.Metric.InwardLocality
import OAI.Geometry.RCD.Harmonic.LocalConstantHarmonic

namespace OAI

/-! # Bounded Sobolev representatives preserving local harmonic coordinates -/

open Set MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Clipping only the global extension leaves a locally bounded coordinate unchanged. -/
def boundedLocalVersion (f : SobolevSpace μ hQ) (C : ℝ≥0) : SobolevSpace μ hQ :=
  SobolevSpace.comp μ hQ (clipReal_lipschitz C) (clipReal_zero C) f

theorem boundedLocalVersion_bound (f : SobolevSpace μ hQ) (C : ℝ≥0) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (boundedLocalVersion μ hQ f C) x| ≤ C := by
  filter_upwards [SobolevSpace.comp_coe μ hQ (clipReal_lipschitz C) (clipReal_zero C) f]
    with x hx
  change |SobolevSpace.toLp μ hQ
    (SobolevSpace.comp μ hQ (clipReal_lipschitz C) (clipReal_zero C) f) x| ≤ C
  rw [hx]
  exact clipReal_abs_le C _

theorem boundedLocalVersion_eq {Ω : Set X} (f : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    SobolevSpace.toLp μ hQ (boundedLocalVersion μ hQ f C) =ᵐ[μ.restrict Ω]
      SobolevSpace.toLp μ hQ f := by
  filter_upwards [hf, ae_restrict_of_ae
    (SobolevSpace.comp_coe μ hQ (clipReal_lipschitz C) (clipReal_zero C) f)] with x hb hx
  exact hx.trans (clipReal_eq_self C hb)

variable [BorelSpace X] [ProperSpace X]

/-- Harmonicity depends only on the local almost-everywhere representative. -/
theorem IsSobolevHarmonicOn.congr_ae {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g : SobolevSpace μ hQ} (hf : IsSobolevHarmonicOn μ hQ Ω f)
    (heq : SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ f) :
    IsSobolevHarmonicOn μ hQ Ω g := by
  have hd : SobolevSpace.toLp μ hQ (g - f) =ᵐ[μ.restrict Ω] fun _ => (0 : ℝ) := by
    filter_upwards [heq, ae_restrict_of_ae
      (Lp.coeFn_sub (SobolevSpace.toLp μ hQ g) (SobolevSpace.toLp μ hQ f))] with x hx hs
    change (SobolevSpace.toLp μ hQ g - SobolevSpace.toLp μ hQ f) x = 0
    simp only [hs, Pi.sub_apply, hx, sub_self]
  have hh := IsSobolevHarmonicOn.add μ hQ
    (isSobolevHarmonicOn_of_local_constant μ hQ Ω hΩ (g - f) 0 hd) hf
  simpa only [sub_add_cancel] using hh

theorem boundedLocalVersion_harmonic {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hh : IsSobolevHarmonicOn μ hQ Ω f) :
    IsSobolevHarmonicOn μ hQ Ω (boundedLocalVersion μ hQ f C) :=
  hh.congr_ae μ hQ hΩ (boundedLocalVersion_eq μ hQ f C hf)

theorem boundedLocalVersion_gamma {Ω : Set X}
    (f a : SobolevSpace μ hQ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    localGamma μ hQ (boundedLocalVersion μ hQ f C) a =ᵐ[μ.restrict Ω]
      localGamma μ hQ f a := by
  filter_upwards [boundedLocalVersion_eq μ hQ f C hf,
    ae_restrict_of_ae (localGamma_eq_on_eq μ hQ (boundedLocalVersion μ hQ f C) f a)]
    with x hx hg
  exact hg hx

/-- Replacing both slots preserves the actual local Gram matrix. -/
theorem boundedLocalVersion_pair {Ω : Set X} (f g : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    localGamma μ hQ (boundedLocalVersion μ hQ f C) (boundedLocalVersion μ hQ g D)
      =ᵐ[μ.restrict Ω] localGamma μ hQ f g := by
  filter_upwards [boundedLocalVersion_gamma μ hQ f (boundedLocalVersion μ hQ g D) C hf,
    ae_restrict_of_ae (localGamma_comm μ hQ f (boundedLocalVersion μ hQ g D)),
    boundedLocalVersion_gamma μ hQ g f D hg,
    ae_restrict_of_ae (localGamma_comm μ hQ g f)] with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end RegularPointCoordinates

end

end OAI
