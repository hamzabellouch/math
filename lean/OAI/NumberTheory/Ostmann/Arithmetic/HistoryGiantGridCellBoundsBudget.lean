import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantGridCellBoundsMixed

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantGridCellBounds
open ScaleBudget Filter PrimeCellMeshBudget PrimeCellActualErrorBudget
open HistoryGiantReplacementError

theorem eventually_giant_grid_errors (k : ℕ) {C K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ (G L₀ : ℝ) (M : ℕ) (E : Finset ℕ),
      0 < M → Real.log (M : ℝ) ≤ Real.exp (giant.μ*L) →
      PrimeBounds k δ K L₀ G L M E → ∀ a : ℕ, a ≤ residueCostExponent k →
      (meshIntervals giant L : ℝ)^2*(M : ℝ)^a*smoothGrowthFactor k C giant.μ L*
        giantPrimeError K δ G E ≤ Real.exp (-Real.exp (giant.target*L)) ∧
      (meshIntervals giant L : ℝ)^2*(M : ℝ)^a*smoothGrowthFactor k C giant.μ L*
        giantMixedError K δ G L E ≤ Real.exp (-Real.exp (giant.target*L)) := by
  let I : ℝ := 2*(6+2*partitionDerivativeConstant)
  let J : ℝ := 2*(Real.exp 1+6+2*partitionDerivativeConstant)
  have hD := partitionDerivativeConstant_pos.le
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  filter_upwards [eventually_primeEnvelope_budget giant k (C:=2)
      (D:=C+residueCostExponent k) (A:=1) (by norm_num) (by norm_num) hK hδ
      giant.μ_pos.le giant.μ_lt_δ.le,
    eventually_primeEnvelope_budget giant k (C:=2) (D:=C+residueCostExponent k)
      (A:=2*J) (by norm_num) (by positivity) hK hδ giant.μ_pos.le giant.μ_lt_δ.le,
    eventually_weighted_integer_decay giant k (C+residueCostExponent k) (2*I)
      giant.μ_pos.le giant.μ_lt_δ.le (by norm_num : (0 : ℝ) < 1)] with L hp hm hi
  intro G L₀ M E hM hmod hb a ha
  let W : ℝ := (meshIntervals giant L : ℝ)^2*(M : ℝ)^a*smoothGrowthFactor k C giant.μ L
  let F : ℝ := jointMeshFactor giant L 2 M*smoothGrowthFactor k (C+residueCostExponent k) giant.μ L
  have hF0 : 0 ≤ F := by dsimp [F,jointMeshFactor,smoothGrowthFactor]; positivity
  have hW := grid_modulus_growth_le k C ha hM hmod
  change W ≤ F at hW
  have hprime := hp 2 M (by omega) hM hmod
  simp only [mul_one] at hprime
  have hprime' : W*giantPrimeError K δ G E ≤ Real.exp (-Real.exp (giant.target*L)) :=
    (mul_le_mul hW hb.error_le_envelope hb.error_nonneg hF0).trans hprime
  have hprime2 : W*(2*J)*giantPrimeError K δ G E ≤ Real.exp (-Real.exp (giant.target*L)) := by
    apply le_trans _ (hm 2 M (by omega) hM hmod)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hW (by positivity))
      hb.error_le_envelope hb.error_nonneg (mul_nonneg hF0 (by positivity))
  have hinteger : W*(2*I)*Real.exp (-Real.exp (giant.a₀*L)) ≤
      Real.exp (-Real.exp (giant.target*L)) := by
    have hh := hi 2 M (by omega) hM hmod
    simp only [neg_one_mul] at hh
    apply le_trans _ hh
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hW (by positivity)) (Real.exp_nonneg _)
  refine ⟨hprime',?_⟩
  change W*giantMixedError K δ G L E ≤ _
  have he : giantMixedError K δ G L E = I*Real.exp (-Real.exp (giant.a₀*L))+
      J*giantPrimeError K δ G E := rfl
  rw [he]
  nlinarith only [hprime2,hinteger]

end Ostmann.Arithmetic.HistoryGiantGridCellBounds

end

end OAI
