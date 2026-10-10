import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReplacementErrorBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantReplacementError
open ScaleBudget PrimeCellMeshBudget PrimeCellActualErrorBudget Filter

theorem eventually_prime_error (k : ℕ) {C A K d : ℝ}
    (hC : 0≤C) (hA : 0≤A) (hK : 0≤K) (hd : 0<d) :
    ∀ᶠ L : ℝ in atTop,∀ (a M : ℕ) (lower Z : ℝ),
      a≤residueCostExponent k → 0<M →
      Real.log (M:ℝ)≤Real.exp (giant.μ*L) → Real.exp (giant.a₀*L)≤lower →
      0<Z → Z⁻¹≤Real.exp (C*((Conclusion.bulkSize k L:ℝ)+1)) →
      (meshIntervals giant L:ℝ)^2*(M:ℝ)^a*smoothGrowthFactor k C giant.μ L*A*
        correctedPrimeError K d lower Z≤Real.exp (-Real.exp (giant.target*L)) := by
  let C' : ℝ := C+residueCostExponent k
  have hC' : 0≤C' := by dsimp [C']; positivity
  filter_upwards [eventually_correctedPrimeError_budget giant k hC' hA hK hd
    giant.μ_pos.le giant.μ_lt_δ.le] with L hL
  intro a M lower Z ha hM hmod hlo hZ hZi
  have hZi' : Z⁻¹≤Real.exp (C'*((Conclusion.bulkSize k L:ℝ)+1)) := by
    refine hZi.trans (Real.exp_le_exp.mpr ?_)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [C']
    linarith [Nat.cast_nonneg (residueCostExponent k) (α:=ℝ)]
  calc
    _ ≤ jointMeshFactor giant L 2 M*smoothGrowthFactor k C' giant.μ L*A*
        correctedPrimeError K d lower Z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (grid_modulus_growth_le k C ha hM hmod) hA)
        (correctedPrimeError_nonneg hK hZ)
    _ ≤ _ := hL 2 M lower Z (by omega) hM hmod hlo hZ hZi'

theorem eventually_variation_error (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,∀ a M : ℕ,
      a≤residueCostExponent k → 0<M → Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
      meshWidth giant L*(M:ℝ)^a*smoothGrowthFactor k C giant.μ L≤
        Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [PrimeCellMeshBudget.eventually_variation_error giant k
    (C+residueCostExponent k) giant.μ_pos.le giant.μ_lt_δ] with L hL
  intro a M ha hM hmod
  calc
    _ = meshWidth giant L*((M:ℝ)^a*smoothGrowthFactor k C giant.μ L) := by ring
    _ ≤ meshWidth giant L*smoothGrowthFactor k (C+residueCostExponent k) giant.μ L :=
      mul_le_mul_of_nonneg_left (modulus_growth_le k C ha hM hmod) (Real.exp_nonneg _)
    _ ≤ _ := by
      convert hL using 1
      unfold meshWidth smoothGrowthFactor
      rw [←Real.exp_add]
      congr 1
      ring

theorem eventually_variation_with_mass (k : ℕ) (C : ℝ) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ L : ℝ in atTop,∀ (a M : ℕ) (mass : ℝ),
      a≤residueCostExponent k → 0<M → Real.log (M:ℝ)≤Real.exp (giant.μ*L) →
      mass≤Real.exp (D*((Conclusion.bulkSize k L:ℝ)+1)) →
      meshWidth giant L*(M:ℝ)^a*smoothGrowthFactor k C giant.μ L*mass≤
        Real.exp (-Real.exp (giant.target*L)) := by
  filter_upwards [eventually_variation_error k (C+D)] with L hL
  intro a M mass ha hM hmod hmass
  calc
    _ ≤ meshWidth giant L*(M:ℝ)^a*smoothGrowthFactor k C giant.μ L*
        Real.exp (D*((Conclusion.bulkSize k L:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hmass (by unfold meshWidth smoothGrowthFactor; positivity)
    _ = (meshWidth giant L*(M:ℝ)^a)*
        (smoothGrowthFactor k C giant.μ L*Real.exp (D*((Conclusion.bulkSize k L:ℝ)+1))) := by ring
    _ ≤ (meshWidth giant L*(M:ℝ)^a)*smoothGrowthFactor k (C+D) giant.μ L :=
      mul_le_mul_of_nonneg_left (smoothGrowth_mul_normalizer_le_add k hD) (by unfold meshWidth; positivity)
    _ ≤ _ := hL a M ha hM hmod

end Ostmann.Arithmetic.HistoryGiantReplacementError

end

end OAI
