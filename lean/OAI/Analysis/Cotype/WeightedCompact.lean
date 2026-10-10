import OAI.Analysis.Cotype.FiniteLevelTower
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

noncomputable section

open scoped BigOperators Topology ENNReal
open Filter
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable (A : ℕ → Submodule ℝ X)

abbrev LevelSum : Type _ := lp (fun l => A l) 2

def levelTerm (l : ℕ) : LevelSum A →L[ℝ] X :=
  (1/2 : ℝ)^l • ((A l).subtypeL.comp (lp.evalCLM ℝ (fun l => A l) 2 l))

omit [CompleteSpace X] in
@[simp] theorem levelTerm_apply (l : ℕ) (z : LevelSum A) :
    levelTerm A l z = (1/2 : ℝ)^l • (z l : X) := rfl

omit [CompleteSpace X] in
theorem levelTerm_norm (l : ℕ) : ‖levelTerm A l‖ ≤ (1/2 : ℝ)^l := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^l)] using
    mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) z l)
      (by positivity : 0 ≤ (1/2 : ℝ)^l)

omit [CompleteSpace X] in
theorem levelTerm_summable_norm : Summable (fun l => ‖levelTerm A l‖) :=
  Summable.of_nonneg_of_le (fun l => norm_nonneg (levelTerm A l)) (levelTerm_norm A)
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))

theorem levelTerm_summable : Summable (levelTerm A) := Summable.of_norm (f := levelTerm A) (levelTerm_summable_norm A)

def weightedMap : LevelSum A →L[ℝ] X := ∑' l, levelTerm A l

omit [CompleteSpace X] in
theorem weightedMap_norm : ‖weightedMap A‖ ≤ 2 := by
  calc
    _ ≤ ∑' l, ‖levelTerm A l‖ := norm_tsum_le_tsum_norm (f := levelTerm A) (levelTerm_summable_norm A)
    _ ≤ ∑' l : ℕ, (1/2 : ℝ)^l := (levelTerm_summable_norm A).tsum_le_tsum (levelTerm_norm A)
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1))
    _ = 2 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)]; norm_num

theorem weightedMap_summable_apply (z : LevelSum A) :
    Summable (fun l => (1/2 : ℝ)^l • (z l : X)) :=
  (ContinuousLinearMap.apply ℝ X z).summable (f := levelTerm A) (levelTerm_summable A)

theorem weightedMap_apply (z : LevelSum A) :
    weightedMap A z = ∑' l, (1/2 : ℝ)^l • (z l : X) := by
  exact ((ContinuousLinearMap.apply ℝ X z).map_tsum (levelTerm_summable A))

omit [CompleteSpace X] in
theorem levelTerm_compact (hA : ∀ l, FiniteDimensional ℝ (A l)) (l : ℕ) :
    IsCompactOperator (levelTerm A l) := by
  let := hA l
  exact ((isCompactOperator_of_locallyCompactSpace_rng (A l).subtypeL).comp_clm
    (lp.evalCLM ℝ (fun l => A l) 2 l)).smul _

theorem weightedMap_compact (hA : ∀ l, FiniteDimensional ℝ (A l)) :
    IsCompactOperator (weightedMap A) := by
  apply isCompactOperator_of_tendsto (levelTerm_summable A).hasSum
  apply Filter.Eventually.of_forall
  intro s
  exact (compactOperator (RingHom.id ℝ) (LevelSum A) X).sum_mem (fun l _ => levelTerm_compact A hA l)

theorem weightedMap_single_zero (x : A 0) :
    weightedMap A (lp.single 2 0 x) = (x : X) := by
  rw [weightedMap_apply, tsum_eq_single 0]
  · simp
  · intro l hl
    simp [lp.single_apply, hl]

end Cotype

end

end OAI
