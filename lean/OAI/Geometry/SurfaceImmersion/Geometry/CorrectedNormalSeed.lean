import OAI.Geometry.SurfaceImmersion.Correction.UniformFreeModeConstants
import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedPerturbedDifference

namespace OAI

/-! Explicit size and difference budgets for the actual corrected normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

def correctedNormalSeed (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b : SupportedField (F := ℝ) K) : SupportedField (F := Ambient 4) K :=
  perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
    (supportedFreeSeed δ τ hF h K hKU b)

def correctedSeedBudget (L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) (N : ℝ) : ℝ :=
  (1 + freeModeBudget 4 L B D q m) *
    (Real.sqrt 2 * 2 ^ (m + (q + 1) * (L + 1)) * N)

lemma correctedSeedBudget_nonneg (L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m)
    (q m : ℕ) {N : ℝ} (hN : 0 ≤ N) : 0 ≤ correctedSeedBudget L B D q m N := by
  have h := freeModeBudget_nonneg 4 L B D hB q m
  dsimp only [correctedSeedBudget]
  positivity

lemma correctedNormalSeed_sub (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b c : SupportedField (F := ℝ) K) :
    correctedNormalSeed δ τ hF h K hKU R q (b - c) =
      correctedNormalSeed δ τ hF h K hKU R q b - correctedNormalSeed δ τ hF h K hKU R q c := by
  simp only [correctedNormalSeed, supportedFreeSeed_sub, map_sub]

theorem correctedNormalSeed_bound (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + 1) (B m))
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (A N : ℝ) (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hbN : WeightedBound U s (m + (q + 1) * (L + 1)) N (freeNormal F))
    (b : SupportedField (F := ℝ) K)
    (hb : supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) b ≤ A) :
    supportedWeightedSeminorm K s m (correctedNormalSeed δ τ hF h K hKU R q b) ≤
      correctedSeedBudget L B D q m N * A * (δ * τ) := by
  have hv := supportedFreeSeed_bound hF h K hKU b hδ hτ.le hs hA hN
    (m + (q + 1) * (L + 1)) hb hbN
  have ht := freeModeBudget_size (contDiff_complexify hF) (h.complexDomain hF)
    K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m
    (supportedFreeSeed δ τ hF h K hKU b) (supportedFreeSeed_isFree δ τ hF h K hKU b)
  have hbudget := freeModeBudget_nonneg 4 L B D hB q m
  calc
    _ ≤ (1 + freeModeBudget 4 L B D q m) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1))
          (supportedFreeSeed δ τ hF h K hKU b) := ht
    _ ≤ (1 + freeModeBudget 4 L B D q m) *
        ((Real.sqrt 2 * 2 ^ (m + (q + 1) * (L + 1)) * A * N) * (δ * τ)) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by dsimp only [correctedSeedBudget]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
