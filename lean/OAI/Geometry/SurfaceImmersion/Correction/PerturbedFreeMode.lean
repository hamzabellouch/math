import OAI.Geometry.SurfaceImmersion.Correction.SupportedInitialMode
import OAI.Geometry.SurfaceImmersion.Geometry.GeometricPerturbedParametrix
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrixPowers

namespace OAI

/-! Finite correction of an actual supported free normal seed in the
presence of the polynomial differential perturbation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

def perturbedFreeMode (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (V : SupportedField (F := Ambient n) K) (q : ℕ) : SupportedField (F := Ambient n) K :=
  FiniteParametrix.improve ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) 0 (initialMode τ h K hKU V 0) q

lemma perturbed_initial_free_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (V : SupportedField (F := Ambient n) K)
    (hX : ∀ x ∈ U, coordDeriv dx G x ⬝ᵥ V x = 0)
    (hY : ∀ x ∈ U, coordDeriv dy G x ⬝ᵥ V x = 0)
    (hV : ∀ x ∈ U, goodSecond G x ⬝ᵥ V x = 0) (m : ℕ) :
    supportedWeightedSeminorm K s m
      (((conjugatedDLM τ hG K).restrictScalars ℝ + R) (initialMode τ h K hKU V 0)) ≤
      (τ / s + ε / τ ^ p) *
        max (fullErrorConstant n m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
        supportedWeightedSeminorm K s (m + (L + 1)) V := by
  have h0 := initialMode_free_residual τ hG h K hKU hτ hs hs1 (hB m) m
    (hc m).toFullModeCoefficientBound V hX hY hV
  have h1 := hR m (initialMode τ h K hKU V 0)
  have hS := initialMode_free_bound τ h K hKU hτ hs hτs hs1 (hB (m + L))
    (m + L) (hc (m + L)) V
  have hnon : 0 ≤ ε / τ ^ p * D m := mul_nonneg (div_nonneg hε (pow_nonneg hτ.le _)) (hD m)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left hS hnon)
  have h0' := h0.trans (mul_le_mul_of_nonneg_left
    (supportedWeightedSeminorm_mono s (show m + 1 ≤ m + (L + 1) by omega) V)
    (mul_nonneg (fullErrorConstant_nonneg _ _ (hB m)) (div_nonneg hτ.le hs.le)))
  change supportedWeightedSeminorm K s m
    (conjugatedDLM τ hG K (initialMode τ h K hKU V 0) + R (initialMode τ h K hKU V 0)) ≤ _
  calc
    _ ≤ supportedWeightedSeminorm K s m (conjugatedDLM τ hG K (initialMode τ h K hKU V 0)) +
        supportedWeightedSeminorm K s m (R (initialMode τ h K hKU V 0)) := map_add_le_add _ _ _
    _ ≤ fullErrorConstant n m (B m) * (τ / s) * supportedWeightedSeminorm K s (m + (L + 1)) V +
        (ε / τ ^ p * D m) * (initialConstant n (m + L) (B (m + L)) *
          supportedWeightedSeminorm K s (m + L + 1) V) := add_le_add h0' h1'
    _ ≤ (τ / s) * max (fullErrorConstant n m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
          supportedWeightedSeminorm K s (m + (L + 1)) V +
        (ε / τ ^ p) * max (fullErrorConstant n m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
          supportedWeightedSeminorm K s (m + (L + 1)) V := by
      rw [Nat.add_assoc]
      apply add_le_add
      · rw [mul_comm (fullErrorConstant n m (B m)) (τ / s)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (div_nonneg hτ.le hs.le)) (apply_nonneg (supportedWeightedSeminorm K s (m + (L + 1))) V)
      · rw [mul_assoc, ← mul_assoc (D m), mul_assoc (ε / τ ^ p)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (apply_nonneg (supportedWeightedSeminorm K s (m + (L + 1))) V))
          (div_nonneg hε (pow_nonneg hτ.le _))
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

end

end OAI
