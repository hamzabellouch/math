import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeOrderBounds
import OAI.Geometry.SurfaceImmersion.Correction.SupportedFreeLinearity

namespace OAI

/-! Seed-independent finite-order estimates for the actual free-mode map. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

theorem perturbedFreeLM_uniform_bound (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z) (q m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : SupportedField (F := Ambient n) K),
      FreeCoefficient G U V →
      supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) ≤
        (τ / s + ε / τ ^ p) * C * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V ∧
      supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V) ≤
        (1 + C) * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  let γ := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  let C := (∑ i ∈ Finset.range q, initialConstant n m (B m) *
    FiniteParametrix.boundProfile (L + 1) κ γ i (m + (L + 1))) + amplitudeConstant n m (B m)
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hγ : ∀ r, 0 ≤ γ r := fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)
  have hC : 0 ≤ C := add_nonneg (Finset.sum_nonneg fun i _ =>
    mul_nonneg (initialConstant_nonneg n m (hB m))
      (FiniteParametrix.boundProfile_nonneg hκ hγ i (m + (L + 1))))
    (amplitudeConstant_nonneg n m (hB m))
  refine ⟨C, hC, ?_⟩
  intro V hV
  have he := perturbedFreeMode_near_seed_order τ hG h K hKU hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR V hV.perpX hV.perpY hV.perpSecond q m
  change supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤
    (τ / s + ε / τ ^ p) * C * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V at he
  rw [← perturbedFreeLM_apply] at he
  refine ⟨he, ?_⟩
  have hn : 0 ≤ C * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V :=
    mul_nonneg hC (apply_nonneg _ _)
  have hmono := supportedWeightedSeminorm_mono s
    (show m ≤ m + (q + 1) * (L + 1) by omega) V
  have he' : supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) ≤
      C * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
    apply he.trans
    simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hsmall hn
  calc
    _ = supportedWeightedSeminorm K s m ((perturbedFreeLM τ hG h K hKU R q V - V) + V) := by
      rw [sub_add_cancel]
    _ ≤ supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) +
        supportedWeightedSeminorm K s m V := map_add_le_add _ _ _
    _ ≤ C * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V +
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := add_le_add he' hmono
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

end

end OAI
