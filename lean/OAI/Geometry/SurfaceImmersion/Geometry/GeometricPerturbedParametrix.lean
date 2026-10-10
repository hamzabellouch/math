import OAI.Geometry.SurfaceImmersion.Correction.SupportedModeBounds
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedTupleOperators
import OAI.Geometry.SurfaceImmersion.Geometry.PerturbedParametrix

namespace OAI

/-! Finite improvement of the actual geometric parametrix in the presence
of a supported differential perturbation. The perturbation estimate is
stated with explicit derivative loss so that polynomial operators can be
inserted without a Banach-space inverse assumption. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

def perturbedMode (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (f : SupportedField (F := Fin 3 → ℂ) K) (q : ℕ) : SupportedField (F := Ambient n) K :=
  FiniteParametrix.improve ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) f
    (forcedModeLM τ hG h K hKU 0 f) q

lemma perturbed_geometric_defect_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (m : ℕ) (f : SupportedField (F := Fin 3 → ℂ) K) :
    supportedWeightedSeminorm K s m
      (FiniteParametrix.defect ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
        ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) f) ≤
      (τ / s + ε / τ ^ p) *
        max (errorConstant m (B m)) (D m * initialConstant n (m + L) (B (m + L))) *
        supportedWeightedSeminorm K s (m + (L + 1)) f := by
  apply FiniteParametrix.perturbed_defect_bound
    ((conjugatedDLM τ hG K).restrictScalars ℝ) R
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ)
    (fun r => supportedWeightedSeminorm K s r) (L + 1)
    (fun r => errorConstant r (B r))
    (fun r => D r * initialConstant n (r + L) (B (r + L)))
    (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  · intro r g
    have hh := geometric_defect_bound τ hG h K hKU hτ hs hs1 (hB r) r
      (hc r).toFullModeCoefficientBound.toModeCoefficientBound g
    calc
      _ ≤ (τ / s) * errorConstant r (B r) * supportedWeightedSeminorm K s (r + 1) g := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (supportedWeightedSeminorm_mono s (by omega) g)
        (mul_nonneg (div_nonneg hτ.le hs.le) (errorConstant_nonneg _ (hB r)))
  · intro r g
    calc
      _ ≤ ε / τ ^ p * D r * supportedWeightedSeminorm K s (r + L)
          (forcedModeLM τ hG h K hKU 0 g) := hR r _
      _ ≤ ε / τ ^ p * D r * (initialConstant n (r + L) (B (r + L)) *
          supportedWeightedSeminorm K s (r + L + 1) g) :=
        mul_le_mul_of_nonneg_left
          (forcedModeLM_zero_bound τ hG h K hKU hτ hs hτs hs1 (hB (r + L)) (r + L) (hc (r + L)) g)
          (mul_nonneg (div_nonneg hε (pow_nonneg hτ.le _)) (hD r))
      _ = _ := by rw [Nat.add_assoc]; ring

/-- Every prescribed finite residual accuracy is achieved by the actual
geometric correction algorithm. Only the derivative budget grows. -/
theorem perturbedMode_residual_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (f : SupportedField (F := Fin 3 → ℂ) K) (q m : ℕ) :
    let η := τ / s + ε / τ ^ p
    let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    supportedWeightedSeminorm K s m
      (((conjugatedDLM τ hG K).restrictScalars ℝ + R)
        (perturbedMode τ hG h K hKU R f q) - f) ≤
      η ^ q * FiniteParametrix.boundProfile (L + 1) κ
        (fun r => η * κ r * supportedWeightedSeminorm K s (r + (L + 1)) f) q m := by
  dsimp only
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hd := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  exact FiniteParametrix.residual_bound
    ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) f
    (forcedModeLM τ hG h K hKU 0 f) (fun r => supportedWeightedSeminorm K s r)
    (L + 1) κ _ hη hκ hd (fun r => hd r f) q m

end ClosedSurfaceR4.SmallModes

end

end OAI
