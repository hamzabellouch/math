import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeModeBounds

namespace OAI

/-! The finite perturbed free mode stays close to its original normal seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

theorem perturbedFreeMode_near_seed (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
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
    supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤
      η * ((∑ i ∈ Finset.range q, initialConstant n m (B m) *
        FiniteParametrix.boundProfile (L + 1) κ C i (m + (L + 1))) +
        amplitudeConstant n m (B m) * supportedWeightedSeminorm K s (m + (L + 1)) V) := by
  let η := τ / s + ε / τ ^ p
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  let C := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))) *
    supportedWeightedSeminorm K s (r + (L + 1)) V
  have hη : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hC : ∀ r, 0 ≤ C r := fun r => mul_nonneg
    ((fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) (apply_nonneg _ _)
  have hdef := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  have hinit := perturbed_initial_free_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR V hX hY hV
  have hS : ∀ r f, supportedWeightedSeminorm K s r (forcedModeLM τ hG h K hKU 0 f) ≤
      initialConstant n r (B r) * supportedWeightedSeminorm K s (r + (L + 1)) f := by
    intro r f
    apply (forcedModeLM_zero_bound τ hG h K hKU hτ hs hτs hs1 (hB r) r (hc r) f).trans
    exact mul_le_mul_of_nonneg_left (supportedWeightedSeminorm_mono s (by omega) f)
      (initialConstant_nonneg _ _ (hB r))
  have hfinite := FiniteParametrix.improve_sub_initial_small
    ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) 0 (initialMode τ h K hKU V 0)
    (fun r => supportedWeightedSeminorm K s r) (fun r => supportedWeightedSeminorm K s r)
    (L + 1) κ C (fun r => initialConstant n r (B r)) hη hsmall hκ hC
    (fun r => initialConstant_nonneg _ _ (hB r)) hdef hS
    (fun r => by simpa only [sub_zero, C, η, mul_assoc] using hinit r) q m
  have hseed := initialMode_free_difference τ h K hKU hτ hs hs1 (hB m) m (hc m) V
  have hseed' : supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0 - V) ≤
      η * (amplitudeConstant n m (B m) * supportedWeightedSeminorm K s (m + (L + 1)) V) := by
    apply hseed.trans
    have hle : τ / s ≤ η := le_add_of_nonneg_right (div_nonneg hε (pow_nonneg hτ.le _))
    calc
      _ ≤ amplitudeConstant n m (B m) * η * supportedWeightedSeminorm K s (m + 1) V :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle
          (amplitudeConstant_nonneg _ _ (hB m))) (apply_nonneg _ _)
      _ ≤ amplitudeConstant n m (B m) * η * supportedWeightedSeminorm K s (m + (L + 1)) V :=
        mul_le_mul_of_nonneg_left (supportedWeightedSeminorm_mono s (by omega) V)
          (mul_nonneg (amplitudeConstant_nonneg _ _ (hB m)) hη)
      _ = _ := by ring
  change supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤ _
  have heq : perturbedFreeMode τ hG h K hKU R V q - V =
      (perturbedFreeMode τ hG h K hKU R V q - initialMode τ h K hKU V 0) +
        (initialMode τ h K hKU V 0 - V) := by abel
  rw [heq]
  calc
    _ ≤ supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - initialMode τ h K hKU V 0) +
        supportedWeightedSeminorm K s m (initialMode τ h K hKU V 0 - V) := map_add_le_add _ _ _
    _ ≤ _ := (add_le_add hfinite hseed').trans_eq (by ring)

end ClosedSurfaceR4.SmallModes

end

end OAI
