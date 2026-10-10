import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeMode

namespace OAI

/-! Residuals of the actual finite free-mode correction gain an arbitrary
fixed power while retaining the same perturbation exponent. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

theorem perturbedFreeMode_residual_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
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
    (hV : ∀ x ∈ U, goodSecond G x ⬝ᵥ V x = 0) (q m : ℕ) :
    let η := τ / s + ε / τ ^ p
    let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    let C := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))) *
      supportedWeightedSeminorm K s (r + (L + 1)) V
    supportedWeightedSeminorm K s m
      (((conjugatedDLM τ hG K).restrictScalars ℝ + R) (perturbedFreeMode τ hG h K hKU R V q)) ≤
      η ^ (q + 1) * FiniteParametrix.boundProfile (L + 1) κ C q m := by
  dsimp only
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hdef := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  have hinit := perturbed_initial_free_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR V hX hY hV
  have hh := FiniteParametrix.residual_bound_succ
    ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) 0
    (initialMode τ h K hKU V 0) (fun r => supportedWeightedSeminorm K s r) (L + 1)
    (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
    (fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))) *
      supportedWeightedSeminorm K s (r + (L + 1)) V)
    hη (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)) hdef
    (fun r => by simpa only [sub_zero, mul_assoc] using hinit r) q m
  simpa only [FiniteParametrix.residual, sub_zero, perturbedFreeMode] using hh

end ClosedSurfaceR4.SmallModes

end

end OAI
