import OAI.Analysis.KadisonKastler.RegularLocalizationAverage
import OAI.Analysis.KadisonKastler.RegularCoreBasis
import OAI.Analysis.KadisonKastler.CountableAmplificationNormal

namespace OAI

/-! # Bounded weak continuity of localization averages

The constant representation is a countable diagonal amplification in
scalar Hilbert coordinates. Its bounded weak continuity therefore gives
bounded weak continuity of the translated-cutoff sandwich. This permits
finite packet compressions to be averaged before taking their limit.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Bounded weak operator limits pass through the constant representation. -/
theorem regularConstantHom_tendsto_weak {ι : Type*} {l : Filter ι}
    (T : ι → H →L[ℂ] H) (S : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x y : H, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (f g : RegularCoreHilbert H) :
    Tendsto (fun i => inner ℂ g (regularConstantHom (volume : Measure ℝ) (T i) f)) l
      (𝓝 (inner ℂ g (regularConstantHom (volume : Measure ℝ) S f))) := by
  let e : RegularCoreHilbert H ≃ₗᵢ[ℂ] CountableHilbertSum H :=
    regularHilbertCoordinates regularScalarBasis
  have he (A : H →L[ℂ] H) :
      inner ℂ (e g) (l2Diagonal A (e f)) =
        inner ℂ g (regularConstantHom (volume : Measure ℝ) A f) := by
    rw [← regularHilbertCoordinates_constant regularScalarBasis A]
    change inner ℂ (e g)
      (e (regularConstantHom (volume : Measure ℝ) A (e.symm (e f)))) = _
    rw [e.symm_apply_apply, e.inner_map_map]
  simpa only [he] using l2Diagonal_tendsto_weak T S C hC hT (e f) (e g)

/-- A localized Haar average preserves every bounded weak operator limit. -/
theorem regularLocalizationAverage_tendsto_weak {ι : Type*} {l : Filter ι}
    (s : Set ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤)
    (T : ι → RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖T i‖ ≤ C)
    (hT : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (S x))))
    (f g : RegularCoreHilbert H) :
    Tendsto (fun i => inner ℂ g (regularLocalizationAverage s hs hfinite (T i) f)) l
      (𝓝 (inner ℂ g (regularLocalizationAverage s hs hfinite S f))) := by
  have h := regularConstantHom_tendsto_weak T S C hC hT
    (regularLocalFrame s hs hfinite f) (regularLocalFrame s hs hfinite g)
  have he (A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
      inner ℂ g (regularLocalizationAverage s hs hfinite A f) =
        inner ℂ (regularLocalFrame s hs hfinite g)
          (regularConstantHom (volume : Measure ℝ) A
            (regularLocalFrame s hs hfinite f)) := by
    change inner ℂ g ((regularLocalFrame s hs hfinite).adjoint
      (A.compLpL 2 (volume : Measure ℝ) (regularLocalFrame s hs hfinite f))) = _
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  simpa only [he] using h

end

end KadisonKastler

end OAI
