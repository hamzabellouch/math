import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeOrderBounds

namespace OAI

/-! The same finite forced correction has a scale-independent amplitude
budget. Only the finite number of required input derivatives grows. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

def forcedModeBudget (n L : ℕ) (B D : ℕ → ℝ) (q m : ℕ) : ℝ :=
  initialConstant n m (B m) +
    ∑ i ∈ Finset.range q, initialConstant n m (B m) *
      FiniteParametrix.boundProfile (L + 1)
        (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
        (fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L))))
        i (m + (L + 1))

lemma forcedModeBudget_nonneg (n L : ℕ) (B D : ℕ → ℝ)
    (hB : ∀ m, 0 ≤ B m) (q m : ℕ) : 0 ≤ forcedModeBudget n L B D q m := by
  apply add_nonneg (initialConstant_nonneg _ _ (hB m))
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (initialConstant_nonneg _ _ (hB m))
  exact FiniteParametrix.boundProfile_nonneg
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _))
    (fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)) _ _

theorem perturbedMode_size (τ : ℝ) {n : ℕ} {G : Field n} {U : Set Base}
    (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) {s : ℝ≥0} {ε : ℝ} {p L : ℕ}
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    (hsmall : τ / s + ε / τ ^ p ≤ 1)
    (B D : ℕ → ℝ) (hB : ∀ m, 0 ≤ B m) (hD : ∀ m, 0 ≤ D m)
    (hc : ∀ m, ReconstructionCoefficientBound G U s (m + 1) (B m))
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (hR : ∀ m Z, supportedWeightedSeminorm K s m (R Z) ≤
      ε / τ ^ p * D m * supportedWeightedSeminorm K s (m + L) Z)
    (f : SupportedField (F := Fin 3 → ℂ) K) (q m : ℕ) :
    supportedWeightedSeminorm K s m (perturbedMode τ hG h K hKU R f q) ≤
      forcedModeBudget n L B D q m *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) f := by
  let A := (conjugatedDLM τ hG K).restrictScalars ℝ + R
  let S := (forcedModeLM τ hG h K hKU 0).restrictScalars ℝ
  let κ := fun r => max (errorConstant r (B r)) (D r * initialConstant n (r + L) (B (r + L)))
  let N := fun r => κ r * supportedWeightedSeminorm K s (r + (L + 1)) f
  have hη : 0 ≤ τ / s + ε / τ ^ p :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hκ : ∀ r, 0 ≤ κ r := fun r => (errorConstant_nonneg _ (hB r)).trans (le_max_left _ _)
  have hd := perturbed_geometric_defect_bound τ hG h K hKU hτ hs hτs hs1 hε B D hB hD hc R hR
  have hS : ∀ r g, supportedWeightedSeminorm K s r (S g) ≤
      initialConstant n r (B r) * supportedWeightedSeminorm K s (r + (L + 1)) g := by
    intro r g
    exact (forcedModeLM_zero_bound τ hG h K hKU hτ hs hτs hs1 (hB r) r (hc r) g).trans
      (mul_le_mul_of_nonneg_left (supportedWeightedSeminorm_mono s (by omega) g)
        (initialConstant_nonneg _ _ (hB r)))
  have hdev := FiniteParametrix.improve_sub_initial_small A S f (S f)
    (fun r => supportedWeightedSeminorm K s r) (fun r => supportedWeightedSeminorm K s r)
    (L + 1) κ N (fun r => initialConstant n r (B r)) hη hsmall hκ
    (fun r => mul_nonneg (hκ r) (apply_nonneg _ _))
    (fun r => initialConstant_nonneg _ _ (hB r)) hd hS (by
      intro r
      simpa only [A, S, N, κ, FiniteParametrix.defect, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearMap.id_apply, mul_assoc] using hd r f) q m
  have hsum := finite_deviation_budget K s (L + 1) q m
    (fun r => initialConstant n r (B r)) κ κ
    (fun r => initialConstant_nonneg _ _ (hB r)) hκ hκ f
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range q, initialConstant n m (B m) *
      FiniteParametrix.boundProfile (L + 1) κ N i (m + (L + 1)) := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (initialConstant_nonneg _ _ (hB m))
      (FiniteParametrix.boundProfile_nonneg hκ (fun r => mul_nonneg (hκ r) (apply_nonneg _ _)) _ _)
  have hdev' : supportedWeightedSeminorm K s m
      (perturbedMode τ hG h K hKU R f q - S f) ≤
      (∑ i ∈ Finset.range q, initialConstant n m (B m) *
        FiniteParametrix.boundProfile (L + 1) κ κ i (m + (L + 1))) *
        supportedWeightedSeminorm K s (m + (q + 1) * (L + 1)) f := by
    exact hdev.trans ((mul_le_of_le_one_left hsum0 hsmall).trans hsum)
  have hinit : supportedWeightedSeminorm K s m (S f) ≤
      initialConstant n m (B m) * supportedWeightedSeminorm K s
        (m + (q + 1) * (L + 1)) f := (hS m f).trans (mul_le_mul_of_nonneg_left
    (supportedWeightedSeminorm_mono s (by
      have hm := Nat.mul_le_mul_right (L + 1) (show 1 ≤ q + 1 by omega)
      omega) f) (initialConstant_nonneg _ _ (hB m)))
  calc
    _ = supportedWeightedSeminorm K s m
        ((perturbedMode τ hG h K hKU R f q - S f) + S f) := by rw [sub_add_cancel]
    _ ≤ supportedWeightedSeminorm K s m (perturbedMode τ hG h K hKU R f q - S f) +
        supportedWeightedSeminorm K s m (S f) := map_add_le_add _ _ _
    _ ≤ _ := add_le_add hdev' hinit
    _ = _ := by dsimp only [forcedModeBudget, κ]; ring

end ClosedSurfaceR4.SmallModes

end

end OAI
