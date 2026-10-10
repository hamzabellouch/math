import OAI.Combinatorics.EditApproximation.Geometry.EarlierInputBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedBandSpacing

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

theorem computed_history_budget_le_height_sq (N : ℕ) (hH : 4 ≤ inputHeight N) :
    (integerParameters N).T + (integerParameters N).S + 1 ≤ inputHeight N ^ 2 := by
  have hT : (integerParameters N).T ≤ 2 * inputHeight N := by
    change 2 ^ ((3 * heightExponent N + 3) / 4) ≤ 2 * 2 ^ heightExponent N
    calc
      _ ≤ 2 ^ (heightExponent N + 1) :=
        pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hS : (integerParameters N).S ≤ inputHeight N := Nat.div_le_self _ _
  nlinarith only [hT, hS, hH]

theorem computed_window_le_height_cube (N : ℕ) (hN : 0 < N)
    (hell : 8 ≤ inputSmallLog N) (hH : 2 ≤ inputHeight N) :
    computedSeedInitialExponent N + 8 ≤ inputHeight N ^ 3 := by
  calc
    _ ≤ 2 * inputSmallLog N ^ 2 := computed_window_exponent_bound N hN hell
    _ ≤ inputHeight N * inputHeight N ^ 2 :=
      Nat.mul_le_mul hH (Nat.pow_le_pow_left (computed_smallLog_le_height N) 2)
    _ = _ := by ring

theorem computed_cell_budget_le_height_pow (N : ℕ) (hH : 64 ≤ inputHeight N) :
    ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 ≤
      inputHeight N ^ 84 := by
  have hconstant : 1296 ≤ inputHeight N ^ 2 :=
    (by norm_num : 1296 ≤ (64 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hH 2)
  calc
    _ ≤ 1296 * inputSmallLog N ^ 82 :=
      computed_local_cell_budget N Nat.one_le_two_pow
    _ ≤ inputHeight N ^ 2 * inputHeight N ^ 82 :=
      Nat.mul_le_mul hconstant (Nat.pow_le_pow_left (computed_smallLog_le_height N) 82)
    _ = _ := by ring

/-- Every literal earlier-input request lies in a cover of cardinality
`H^(256(p+1))`. The only value premise is nonnegativity of the actual
initial query value; no good-seed event is required. -/
theorem computed_queryEarlierInputCover_card {nx ny : ℕ}
    (parent : TargetInterval nx) (N P : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hPeq : P = (integerParameters N).P)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hw : 0 ≤ initial q) :
    (queryEarlierInputCover (M := (integerParameters N).M) parent N P (inputSmallLog N)
      (40 * smallLogExponent N) ((integerParameters N).T + (integerParameters N).S + 1)
      (refinementFactor A (inputSmallLog N)) initial q).card ≤
      inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) := by
  let W := computedSeedInitialExponent N + 8
  let C := ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2
  have hF : inputSmallLog N ≤ inputHeight N := computed_smallLog_le_height N
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans hF
  have hPpos : 1 ≤ P := by
    rw [hPeq]
    exact one_le_pow₀ Nat.one_le_two_pow
  have hPpower : P ≤ inputHeight N ^ (coarseExponent (inputSmallLog N) + 20) := by
    rw [hPeq]
    exact le_rfl
  have hM : (integerParameters N).M ≤ inputHeight N :=
    pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hbudget := queryEarlierInputCover_le_budget (M := (integerParameters N).M)
    parent N P (inputSmallLog N) (40 * smallLogExponent N)
    ((integerParameters N).T + (integerParameters N).S + 1) W C
    (refinementFactor A (inputSmallLog N)) initial q
    ⟨_, hPeq.trans (computed_P_dyadic N)⟩ (by omega) hw
    (computed_refinement_window N hN (by omega) A (initial q) hA) le_rfl
  exact hbudget.trans (localEarlierBudget_poly (inputHeight N)
    (coarseExponent (inputSmallLog N)) W C (integerParameters N).M P (inputSmallLog N)
    ((integerParameters N).T + (integerParameters N).S + 1)
    hH hPpos hPpower (computed_window_le_height_cube N hN (by omega) (by omega))
    (computed_cell_budget_le_height_pow N hH) hM hF
    (computed_history_budget_le_height_sq N (by omega)))

end EditApproximation

end OAI
