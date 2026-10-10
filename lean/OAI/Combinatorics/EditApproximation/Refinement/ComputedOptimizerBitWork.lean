import OAI.Combinatorics.EditApproximation.Numerics.OptimizerBitEnvelope
import OAI.Combinatorics.EditApproximation.Geometry.LocalWorkEnvelope

namespace OAI

/-! Substitution of the actual grid and optimizer parameters into the
Boolean-operation envelope. Input word bounds remain explicit here so
the local rational-value invariants can supply them without a unit-cost
rational arithmetic assumption. -/

namespace EditApproximation

open Filter
open scoped Topology

def localBooleanBitExponent (M p C : ℕ) : ℕ :=
  ((44 * M + C + 4000) * (p + 1)) * optimizerBitPolynomialDegree

theorem optimizerBitBudget_grid_cap (H M P p C d v G K B Bv L V : ℕ)
    (hH : 64 ≤ H) (hM : M ≤ H) (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20))
    (hd : d ≤ M * (40 * P + 2) ^ 2) (hv : v ≤ (40 * P + 2) ^ (2 * M))
    (hG : G ≤ H + M * (40 * P + 2) ^ 2 + 4) (hK : K ≤ G ^ 80)
    (hB : B ≤ H ^ (C * (p + 1))) (hBv : Bv ≤ H ^ (C * (p + 1)))
    (hL : L ≤ H ^ (C * (p + 1))) (hV : V ≤ H ^ (C * (p + 1))) :
    BinaryFraction.optimizerBitBudget d v G K B Bv L V ≤ H ^ localBooleanBitExponent M p C := by
  let E := (44 * M + C + 4000) * (p + 1)
  have hHpos : 0 < H := by omega
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hc : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hc hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H _ _).symm
      _ = _ := by congr 1; omega
  have hv' : v ≤ H ^ E := by
    calc
      _ ≤ (H ^ (p + 22)) ^ (2 * M) := hv.trans (Nat.pow_le_pow_left hbox _)
      _ = H ^ ((p + 22) * (2 * M)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHpos (by dsimp only [E]; nlinarith)
  have hd' : d ≤ H ^ E :=
    (hd.trans (wide_coordinate_budget_le H M P p hH hM hP hPcap)).trans
      (Nat.pow_le_pow_right hHpos (by dsimp only [E]; nlinarith))
  have hG0 := hG.trans (optimizer_parameter_budget_le H M P p hH hM hP hPcap)
  have hG' : G ≤ H ^ E := hG0.trans
    (Nat.pow_le_pow_right hHpos (by dsimp only [E]; nlinarith))
  have hK' : K ≤ H ^ E := by
    calc
      _ ≤ (H ^ (2 * p + 46)) ^ 80 := hK.trans (Nat.pow_le_pow_left hG0 _)
      _ = H ^ ((2 * p + 46) * 80) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHpos (by dsimp only [E]; nlinarith)
  have hE : C * (p + 1) ≤ E := by dsimp only [E]; nlinarith
  have hS : 2 ≤ H ^ E := by
    have he : 1 ≤ E := by dsimp only [E]; nlinarith
    exact (by omega : 2 ≤ H).trans (Nat.le_pow he)
  have h := optimizerBitBudget_le_fixed_power d v G K B Bv L V (H ^ E) hS hd' hv' hG' hK'
    (hB.trans (Nat.pow_le_pow_right hHpos hE))
    (hBv.trans (Nat.pow_le_pow_right hHpos hE))
    (hL.trans (Nat.pow_le_pow_right hHpos hE))
    (hV.trans (Nat.pow_le_pow_right hHpos hE))
  simpa only [← pow_mul, E, localBooleanBitExponent] using h

noncomputable def computedBooleanBitExponent (C N : ℕ) : ℝ :=
  (optimizerBitPolynomialDegree : ℝ) *
    ((44 * Real.log 2) * ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N +
      ((C : ℝ) + 4000) * ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
        Real.log (inputHeight N : ℝ))

theorem computedBooleanBitExponent_tendsto (C : ℕ) :
    Tendsto (fun N => computedBooleanBitExponent C N / inputHeight N) atTop (𝓝 0) := by
  have h := ((local_enumeration_exponent_div_height_tendsto.const_mul (44 * Real.log 2)).add
    (encoding_exponent_div_height_tendsto.const_mul ((C : ℝ) + 4000))).const_mul
      (optimizerBitPolynomialDegree : ℝ)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  ext N
  unfold computedBooleanBitExponent
  ring

def computedBooleanBitBudget (C N : ℕ) : ℕ :=
  inputHeight N ^ localBooleanBitExponent (integerParameters N).M
    (coarseExponent (inputSmallLog N)) C

private theorem booleanBitBudget_exp_scalar (D C H M p ell : ℕ) (hH : 0 < H)
    (hlog : Real.log (H : ℝ) ≤ (ell : ℝ) * Real.log 2) :
    ((H ^ (((44 * M + C + 4000) * (p + 1)) * D) : ℕ) : ℝ) ≤
      Real.exp ((D : ℝ) * ((44 * Real.log 2) * (M : ℝ) * ((p : ℝ) + 1) * ell +
        ((C : ℝ) + 4000) * ((p : ℝ) + 1) * Real.log (H : ℝ))) := by
  rw [Nat.cast_pow, nat_pow_eq_exp_log H _ hH]
  apply Real.exp_le_exp.mpr
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (p : ℝ) + 1 := by have h := Nat.cast_nonneg (α := ℝ) p; linarith
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 44) hM) hp)
  have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith only [mul_nonneg hD (sub_nonneg.mpr hmul)]

theorem computedBooleanBitBudget_exp_bound (C N : ℕ) (hN : 0 < N) :
    (computedBooleanBitBudget C N : ℝ) ≤ Real.exp (computedBooleanBitExponent C N) := by
  have hH : 0 < inputHeight N := by
    dsimp only [inputHeight]
    exact Nat.pow_pos (by decide : 0 < (2 : ℕ))
  have hlog : Real.log (inputHeight N : ℝ) ≤ (inputSmallLog N : ℝ) * Real.log 2 := by
    rw [inputHeight_real_log]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (inputSmallLog_bounds N hN).1)
      (Real.log_nonneg (by norm_num))
  exact booleanBitBudget_exp_scalar optimizerBitPolynomialDegree C (inputHeight N)
    (integerParameters N).M (coarseExponent (inputSmallLog N)) (inputSmallLog N) hH hlog

theorem computedBooleanBitBudget_subpolynomial (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, (computedBooleanBitBudget C N : ℝ) ≤ (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input (computedBooleanBitExponent C)
    (computedBooleanBitExponent_tendsto C) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  exact (computedBooleanBitBudget_exp_bound C N (by omega)).trans he

theorem computedBooleanBitBudget_widthWork_near_linear (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) * computedBooleanBitBudget C N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computed_widthWork_subexponential (computedBooleanBitExponent C)
    (computedBooleanBitExponent_tendsto C) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  intro n hn tree hv hd hk
  exact (mul_le_mul_of_nonneg_left (computedBooleanBitBudget_exp_bound C N (by omega))
    (Nat.cast_nonneg _)).trans (he n hn tree hv hd hk)

end EditApproximation

end OAI
