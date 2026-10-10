import OAI.Geometry.SurfaceImmersion.Geometry.CorrectedNormalSeed
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialModeResidual

namespace OAI

/-! Transport the actual corrected normal seed to the polynomial jet coordinates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma inverse_supportedCoordinateEquiv_norm {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) (K : Compacts A) {s : ℝ≥0} (hs : 0 < (s : ℝ)) (m : ℕ)
    (f : SupportedField (F := F) (K.map e e.continuous)) :
    supportedWeightedSeminorm K s m ((supportedCoordinateEquiv e K).symm f) =
      supportedWeightedSeminorm (K.map e e.continuous) s m f := by
  have hh := supportedCoordinateEquiv_norm e K hs m ((supportedCoordinateEquiv e K).symm f)
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

namespace Perturbation
open RealModes SmallModes
variable {F : RField 4} {V : Set SmallModes.Base}

def coordinateCorrectedSeed (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) : SupportedField (F := Fin 4 → ℂ) K :=
  (supportedCoordinateEquiv planeCoordinateIsometry K).symm
    (correctedNormalSeed δ τ hF h (modeSupport K) hKV R q b)

lemma coordinateCorrectedSeed_sub (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b c : SupportedField (F := ℝ) (modeSupport K)) :
    coordinateCorrectedSeed δ τ hF h K hKV R q (b - c) =
      coordinateCorrectedSeed δ τ hF h K hKV R q b -
        coordinateCorrectedSeed δ τ hF h K hKV R q c := by
  simp only [coordinateCorrectedSeed, correctedNormalSeed_sub, map_sub]

lemma coordinateCorrectedSeed_bound (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) V s (m + 1) (B m))
    (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (hR : ∀ m Z, supportedWeightedSeminorm (modeSupport K) s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm (modeSupport K) s (m + L) Z)
    (q m : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hbN : WeightedBound V s (m + (q + 1) * (L + 1)) N (freeNormal F))
    (b : SupportedField (F := ℝ) (modeSupport K))
    (hb : supportedWeightedSeminorm (modeSupport K) s (m + (q + 1) * (L + 1)) b ≤ A) :
    supportedWeightedSeminorm K s m (coordinateCorrectedSeed δ τ hF h K hKV R q b) ≤
      correctedSeedBudget L B D q m N * A * (δ * τ) := by
  rw [coordinateCorrectedSeed, inverse_supportedCoordinateEquiv_norm _ _ hs]
  exact correctedNormalSeed_bound δ τ hF h (modeSupport K) hKV hδ hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR q m A N hA hN hbN b hb

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
