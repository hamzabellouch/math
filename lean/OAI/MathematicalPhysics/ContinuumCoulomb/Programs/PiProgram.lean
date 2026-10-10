import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalQuadratureProgram
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! A rational polynomial-time approximation to π from the integral of
`4 / (1+x²)` on `[0,1]`. The unary sample count gives absolute error `8/N`.
This supplies the normalizing constant in the heat-kernel evaluator. -/

namespace ContinuumCoulomb.PiProgram
open ExactQuantumFactoring.BitStackProgram
open RationalQuadratureProgram

def evaluate (_ : ℚ) (q : ℚ) : ℚ := (1 + q ^ 2)⁻¹

def input (N : ℕ) : Input ℚ := (N, 0, 0, (N : ℚ)⁻¹)

def approximate (N : ℕ) : ℚ := 4 * value evaluate (input N)

noncomputable def evaluateProgram :
    Procedure (prodCode ratCode ratCode) ratCode (fun x => evaluate x.1 x.2) := by
  let q := Procedure.second ratCode ratCode
  let square := Procedure.ratMul.comp (q.pair q)
  let one := Procedure.constant (prodCode ratCode ratCode) ratCode (1 : ℚ)
  exact (Procedure.ratInv.comp (Procedure.ratAdd.comp (one.pair square))).congrFun
    (by intro x; simp only [evaluate, pow_two]; rfl)

noncomputable def inputProgram : Procedure unaryCode (inputCode ratCode) input := by
  let n := Procedure.identity unaryCode
  let zero := Procedure.constant unaryCode ratCode (0 : ℚ)
  let reciprocal := Procedure.ratInv.comp (Procedure.natToRat.comp Procedure.unaryToBits)
  exact (n.pair (zero.pair (zero.pair reciprocal))).congrFun (by intro N; rfl)

noncomputable def program : Procedure unaryCode ratCode approximate := by
  let q := (RationalQuadratureProgram.program ratCode evaluate evaluateProgram).comp inputProgram
  let four := Procedure.constant unaryCode ratCode (4 : ℚ)
  exact (Procedure.ratMul.comp (four.pair q)).congrFun (by intro N; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime unaryCode ratCode approximate := program.toTM2

theorem reciprocal_continuous : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
  ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).add
    (continuous_id.pow 2)).inv₀ (by intro x; change (1 : ℝ) + x ^ 2 ≠ 0; positivity)

theorem reciprocal_lipschitz (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |(1 + x ^ 2)⁻¹ - (1 + y ^ 2)⁻¹| ≤ 2 * |x - y| := by
  have hx0 : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hy0 : (1 : ℝ) + y ^ 2 ≠ 0 := by positivity
  have hid : (1 + x ^ 2)⁻¹ - (1 + y ^ 2)⁻¹ =
      ((y - x) * (y + x)) / ((1 + x ^ 2) * (1 + y ^ 2)) := by
    field_simp
    ring
  have hd : 1 ≤ (1 + x ^ 2) * (1 + y ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  rw [hid, abs_div, abs_mul, abs_of_nonneg (show 0 ≤ y + x by linarith [hx.1, hy.1]),
    abs_of_pos (show 0 < (1 + x ^ 2) * (1 + y ^ 2) by linarith), abs_sub_comm y x]
  apply (div_le_iff₀ (show 0 < (1 + x ^ 2) * (1 + y ^ 2) by linarith)).mpr
  have hnum := mul_le_mul_of_nonneg_left (show y + x ≤ (2 : ℝ) by linarith [hx.2, hy.2])
    (abs_nonneg (x - y))
  have hden := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * |x - y| by positivity)
  nlinarith

theorem endpoint (N : ℕ) (hN : 0 < N) : node (0 : ℚ) (N : ℚ)⁻¹ N = 1 := by
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [node, hn]

theorem error (N : ℕ) (hN : 0 < N) :
    |(approximate N : ℝ) - Real.pi| ≤ 8 / (N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := RationalQuadratureProgram.error evaluate (input N)
    (fun x : ℝ => (1 + x ^ 2)⁻¹) (L := 2) (ε := 0)
    (by dsimp [input]; positivity) (by norm_num) reciprocal_continuous
    (by
      intro x hx y hy
      simp only [input, endpoint N hN, Rat.cast_zero, Rat.cast_one] at hx hy
      exact reciprocal_lipschitz x y hx hy)
    (by
      intro i hi
      simp [sample, evaluate, input])
  have hi : (∫ x : ℝ in (0 : ℝ)..1, (1 + x ^ 2)⁻¹) = Real.pi / 4 := by
    rw [integral_inv_one_add_sq, Real.arctan_one, Real.arctan_zero, sub_zero]
  simp only [input, endpoint N hN, Rat.cast_zero, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast,
    mul_zero, add_zero, hi] at h
  have heq : (approximate N : ℝ) - Real.pi =
      4 * ((value evaluate (input N) : ℝ) - Real.pi / 4) := by
    simp only [approximate, Rat.cast_mul, Rat.cast_ofNat]
    ring
  rw [heq, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)
  have hs : 4 * ((N : ℝ) * (2 * (N : ℝ)⁻¹ ^ 2)) = 8 / (N : ℝ) := by
    field_simp
    ring
  exact hm.trans_eq hs

end ContinuumCoulomb.PiProgram

end OAI
