import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeOrderBounds
import OAI.Geometry.SurfaceImmersion.Correction.SupportedFreeLinearity

namespace OAI

/-! Explicit free-mode constants, independent of both short scales and
of the perturbation size. These constants are used before selecting scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

def freeModeBudget (n L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range q, initialConstant n m (B m) *
    FiniteParametrix.boundProfile (L + 1)
      (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
      (fun r => max (fullErrorConstant n r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
      i (m + (L + 1))) + amplitudeConstant n m (B m)

lemma freeModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (q m : ℕ) :
    0 ≤ freeModeBudget n L B D q m := by
  apply add_nonneg _ (amplitudeConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (fullErrorConstant_nonneg _ _ (hB r)).trans (le_max_left _ _)) _ _

theorem freeModeBudget_bound {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε τ : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (V : SupportedField (F := Ambient n) K) (hV : FreeCoefficient G U V) :
    supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) ≤
      (τ / s + ε / τ ^ p) * freeModeBudget n L B D q m *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  rw [perturbedFreeLM_apply]
  exact perturbedFreeMode_near_seed_order τ hG h K hKU hτ hs hτs hs1 hε hsmall
    B D hB hD hc R hR V hV.perpX hV.perpY hV.perpSecond q m


theorem freeModeBudget_size {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε τ : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (q m : ℕ) (V : SupportedField (F := Ambient n) K) (hV : FreeCoefficient G U V) :
    supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V) ≤
      (1 + freeModeBudget n L B D q m) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
  have hh := freeModeBudget_bound hG h K hKU hτ hs hτs hs1 hε hsmall B D hB hD hc R hR q m V hV
  have hn : 0 ≤ freeModeBudget n L B D q m *
      supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V :=
    mul_nonneg (freeModeBudget_nonneg n L B D hB q m) (apply_nonneg _ _)
  have he : supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) ≤
      freeModeBudget n L B D q m * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := by
    apply hh.trans
    simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hsmall hn
  have hmono := supportedWeightedSeminorm_mono s
    (show m ≤ m + (q + 1) * (L + 1) by omega) V
  calc
    _ = supportedWeightedSeminorm K s m ((perturbedFreeLM τ hG h K hKU R q V - V) + V) := by
      rw [sub_add_cancel]
    _ ≤ supportedWeightedSeminorm K s m (perturbedFreeLM τ hG h K hKU R q V - V) +
        supportedWeightedSeminorm K s m V := map_add_le_add _ _ _
    _ ≤ freeModeBudget n L B D q m * supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V +
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) V := add_le_add he hmono
    _ = _ := by ring

end ClosedSurfaceR4.SmallModes

end

end OAI
