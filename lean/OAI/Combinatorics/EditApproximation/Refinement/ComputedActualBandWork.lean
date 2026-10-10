import OAI.Combinatorics.EditApproximation.Geometry.ActualBandBitEnvelope
import OAI.Combinatorics.EditApproximation.Refinement.ComputedOptimizerBitWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCacheWords

namespace OAI

/-! The same grid and dependency exponents control the full Boolean call,
including exact envelope construction, vertices and the optimistic-history input. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_dyadicScale_bits (N b : ℕ) (hN : 0 < N) (hb : b ∈ dyadicScales N) :
    Nat.size b ≤ inputHeight N := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
  have hk' : k ≤ Nat.log 2 N := by
    have := List.mem_range.mp hk
    omega
  have hvalue := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk').trans
    (Nat.pow_log_le_self 2 hN.ne')
  exact (Nat.size_le_size hvalue).trans (computed_input_size_le_height N)

def localActualBandBitExponent (M p C : ℕ) : ℕ :=
  ((44 * M + C + 4000) * (p + 1)) * actualBandOptimizerBitDegree

theorem actualBandOptimizerBitBudget_grid_cap (H M P p C d b v G K t Be Bk Bi Bt E : ℕ)
    (hH : 64 ≤ H) (hM : M ≤ H) (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20))
    (hd : d ≤ M * (40 * P + 2) ^ 2) (hv : v ≤ (40 * P + 2) ^ (2 * M))
    (hG : G ≤ H + M * (40 * P + 2) ^ 2 + 4) (hK : K ≤ G ^ 80) (ht : t ≤ H) (hb : Nat.size b ≤ H)
    (hBe : Be ≤ H ^ (C * (p + 1))) (hBk : Bk ≤ H ^ (C * (p + 1)))
    (hBi : Bi ≤ H ^ (C * (p + 1))) (hBt : Bt ≤ H ^ (C * (p + 1)))
    (hE : E ≤ H ^ (C * (p + 1))) :
    BinaryFraction.actualBandOptimizerBitBudget M d b v G K t Be Bk Bi Bt E ≤
      H ^ localActualBandBitExponent M p C := by
  let exponent := (44 * M + C + 4000) * (p + 1)
  have hHpos : 0 < H := by omega
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hc : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hc hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H _ _).symm
      _ = _ := by congr 1; omega
  have hv' : v ≤ H ^ exponent := by
    calc
      _ ≤ (H ^ (p + 22)) ^ (2 * M) := hv.trans (Nat.pow_le_pow_left hbox _)
      _ = H ^ ((p + 22) * (2 * M)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHpos (by dsimp only [exponent]; nlinarith)
  have hd' : d ≤ H ^ exponent :=
    (hd.trans (wide_coordinate_budget_le H M P p hH hM hP hPcap)).trans
      (Nat.pow_le_pow_right hHpos (by dsimp only [exponent]; nlinarith))
  have hG0 := hG.trans (optimizer_parameter_budget_le H M P p hH hM hP hPcap)
  have hG' : G ≤ H ^ exponent := hG0.trans
    (Nat.pow_le_pow_right hHpos (by dsimp only [exponent]; nlinarith))
  have hK' : K ≤ H ^ exponent := by
    calc
      _ ≤ (H ^ (2 * p + 46)) ^ 80 := hK.trans (Nat.pow_le_pow_left hG0 _)
      _ = H ^ ((2 * p + 46) * 80) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHpos (by dsimp only [exponent]; nlinarith)
  have hC : C * (p + 1) ≤ exponent := by dsimp only [exponent]; nlinarith
  have hheight : H ≤ H ^ exponent := Nat.le_pow (by dsimp only [exponent]; nlinarith)
  have hS : 64 ≤ H ^ exponent := hH.trans hheight
  have h := actualBandOptimizerBitBudget_le_fixed_power M d b v G K t Be Bk Bi Bt E
    (H ^ exponent) hS (hM.trans hheight) hd' (hb.trans hheight) hv' hG' hK' (ht.trans hheight)
    (hBe.trans (Nat.pow_le_pow_right hHpos hC))
    (hBk.trans (Nat.pow_le_pow_right hHpos hC))
    (hBi.trans (Nat.pow_le_pow_right hHpos hC))
    (hBt.trans (Nat.pow_le_pow_right hHpos hC))
    (hE.trans (Nat.pow_le_pow_right hHpos hC))
  simpa only [← pow_mul, exponent, localActualBandBitExponent] using h

noncomputable def computedActualBandBitExponent (C N : ℕ) : ℝ :=
  (actualBandOptimizerBitDegree : ℝ) *
    ((44 * Real.log 2) * ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N +
      ((C : ℝ) + 4000) * ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
        Real.log (inputHeight N : ℝ))

theorem computedActualBandBitExponent_tendsto (C : ℕ) :
    Tendsto (fun N => computedActualBandBitExponent C N / inputHeight N) atTop (𝓝 0) := by
  have h := ((local_enumeration_exponent_div_height_tendsto.const_mul (44 * Real.log 2)).add
    (encoding_exponent_div_height_tendsto.const_mul ((C : ℝ) + 4000))).const_mul
      (actualBandOptimizerBitDegree : ℝ)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  ext N
  unfold computedActualBandBitExponent
  ring

def computedActualBandBitBudget (C N : ℕ) : ℕ :=
  inputHeight N ^ localActualBandBitExponent (integerParameters N).M
    (coarseExponent (inputSmallLog N)) C

private theorem actualBandBitBudget_exp_scalar (D C H M p ell : ℕ) (hH : 0 < H)
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

theorem computedActualBandBitBudget_exp_bound (C N : ℕ) (hN : 0 < N) :
    (computedActualBandBitBudget C N : ℝ) ≤ Real.exp (computedActualBandBitExponent C N) := by
  have hH : 0 < inputHeight N := by
    dsimp only [inputHeight]
    exact Nat.pow_pos (by decide : 0 < (2 : ℕ))
  have hlog : Real.log (inputHeight N : ℝ) ≤ (inputSmallLog N : ℝ) * Real.log 2 := by
    rw [inputHeight_real_log]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (inputSmallLog_bounds N hN).1)
      (Real.log_nonneg (by norm_num))
  exact actualBandBitBudget_exp_scalar actualBandOptimizerBitDegree C (inputHeight N)
    (integerParameters N).M (coarseExponent (inputSmallLog N)) (inputSmallLog N) hH hlog

theorem computedActualBandBitBudget_subpolynomial (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, (computedActualBandBitBudget C N : ℝ) ≤ (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input (computedActualBandBitExponent C)
    (computedActualBandBitExponent_tendsto C) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  exact (computedActualBandBitBudget_exp_bound C N (by omega)).trans he

theorem computedActualBandBitBudget_widthWork_near_linear (C : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) * computedActualBandBitBudget C N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computed_widthWork_subexponential (computedActualBandBitExponent C)
    (computedActualBandBitExponent_tendsto C) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  intro n hn tree hv hd hk
  exact (mul_le_mul_of_nonneg_left (computedActualBandBitBudget_exp_bound C N (by omega))
    (Nat.cast_nonneg _)).trans (he n hn tree hv hd hk)

end EditApproximation

end OAI
