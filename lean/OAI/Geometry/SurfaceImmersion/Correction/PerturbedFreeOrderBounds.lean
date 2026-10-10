import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeModeSize
import OAI.Geometry.SurfaceImmersion.Primitive.FiniteProfileBounds

namespace OAI

/-! Finite derivative orders and seed-independent constants for the free correction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

lemma finite_deviation_budget {n : ℕ} (K : Compacts Base) (s : ℝ≥0) (L q m : ℕ)
    (B κ γ : ℕ → ℝ) (hB : ∀ r, 0 ≤ B r) (hκ : ∀ r, 0 ≤ κ r) (hγ : ∀ r, 0 ≤ γ r)
    (V : SupportedField (F := Ambient n) K) :
    (∑ i ∈ Finset.range q, B m * FiniteParametrix.boundProfile L κ
      (fun r => γ r * supportedWeightedSeminorm K s (r + L) V) i (m + L)) ≤
    (∑ i ∈ Finset.range q, B m * FiniteParametrix.boundProfile L κ γ i (m + L)) *
      supportedWeightedSeminorm K s (m + (q + 1) * L) V := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [FiniteParametrix.boundProfile_terminal L κ γ
    (fun r => supportedWeightedSeminorm K s r V), ← mul_assoc]
  apply mul_le_mul_of_nonneg_left
  · apply supportedWeightedSeminorm_mono s _ V
    have hi' := Finset.mem_range.mp hi
    have hmul := Nat.mul_le_mul_right L (show i + 2 ≤ q + 1 by omega)
    convert Nat.add_le_add_left hmul m using 1
    ring
  · exact mul_nonneg (hB m) (FiniteParametrix.boundProfile_nonneg hκ hγ i (m + L))

theorem perturbedFreeMode_near_seed_order (τ : ℝ) {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
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
    let γ := fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
    supportedWeightedSeminorm K s m (perturbedFreeMode τ hG h K hKU R V q - V) ≤
      η * ((∑ i ∈ Finset.range q, initialConstant n m (B m) *
        FiniteParametrix.boundProfile (L + 1) κ γ i (m + (L + 1))) + amplitudeConstant n m (B m)) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  dsimp only
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  apply (perturbedFreeMode_near_seed τ hG h K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR V hX hY hV q m).trans
  have hsum := finite_deviation_budget K s (L + 1) q m
    (fun r => initialConstant n r (B r))
    (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
    (fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
    (fun r => initialConstant_nonneg _ _ (hB r))
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) V
  have hseed := mul_le_mul_of_nonneg_left
    (supportedWeightedSeminorm_mono s (show m + (L + 1) ≤ m + (q + 1) * (L + 1) by
      have hh := Nat.mul_le_mul_right (L + 1) (show 1 ≤ q + 1 by omega)
      omega) V) (amplitudeConstant_nonneg n m (hB m))
  calc
    _ ≤ (τ / s + ε / τ ^ p) * (_ * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V +
        amplitudeConstant n m (B m) * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V) :=
      mul_le_mul_of_nonneg_left (add_le_add hsum hseed) hη
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

end

end OAI
