import Mathlib
import OAI.MathematicalPhysics.BFSS.ColorMatrices

namespace OAI

/-! Color Lie algebra, skew adjoints and commutators. -/

namespace BFSSQuantum
noncomputable section
open Matrix Finset
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

abbrev ColorVector (N : ℕ) := EuclideanSpace ℝ (ColorIndex N)

def colorEmbed : ColorVector N →ₗ[ℝ] ColorMatrix N where
  toFun x := M.colorCombination x
  map_add' x y := by
    simp only [colorCombination, PiLp.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    change M.colorCombination (fun A => r * x A) = r • M.colorCombination x
    rw [M.colorCombination_smul]
    rfl

lemma colorEmbed_injective : Function.Injective M.colorEmbed := by
  intro a b h
  ext A
  have hh := congrArg (fun X => (Matrix.trace (M.color A * X)).re) h
  exact (M.colorCombination_coeff a A).symm.trans (hh.trans (M.colorCombination_coeff b A))

lemma colorEmbed_inner (a b : ColorVector N) :
    (inner ℝ a b : ℂ) = Matrix.trace (M.colorEmbed a * M.colorEmbed b) := by
  rw [show M.colorEmbed a = M.colorCombination a from rfl,
    show M.colorEmbed b = M.colorCombination b from rfl, M.colorCombination_pairing]
  simp [PiLp.inner_apply,mul_comm]

def colorLie (a b : ColorVector N) : ColorVector N :=
  WithLp.toLp 2 (fun A => ∑ B, ∑ C, M.structureConstant A B C * a B * b C)

lemma colorEmbed_lie (a b : ColorVector N) :
    M.colorEmbed (M.colorLie a b) = AlgebraData.bracket (M.colorEmbed a) (M.colorEmbed b) :=
  (M.bracket_colorCombination a b).symm

lemma bracket_add_left (x y z : ColorMatrix N) :
    AlgebraData.bracket (x+y) z = AlgebraData.bracket x z + AlgebraData.bracket y z := by
  simp only [bracket, add_mul, mul_add, smul_sub, smul_add]
  abel
lemma bracket_add_right (x y z : ColorMatrix N) :
    AlgebraData.bracket x (y+z) = AlgebraData.bracket x y + AlgebraData.bracket x z := by
  simp only [bracket, add_mul, mul_add, smul_sub, smul_add]
  abel
lemma bracket_neg_swap (x y : ColorMatrix N) :
    AlgebraData.bracket x y = -AlgebraData.bracket y x := by
  simp only [bracket, smul_sub]
  abel
lemma bracket_real_smul_right (r : ℝ) (x y : ColorMatrix N) :
    AlgebraData.bracket x (r • y) = r • AlgebraData.bracket x y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, ←smul_sub]
  exact smul_comm _ _ _
lemma bracket_real_smul_left (r : ℝ) (x y : ColorMatrix N) :
    AlgebraData.bracket (r • x) y = r • AlgebraData.bracket x y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, ←smul_sub]
  exact smul_comm _ _ _
lemma bracket_jacobi (x y z : ColorMatrix N) :
    AlgebraData.bracket x (AlgebraData.bracket y z) -
      AlgebraData.bracket y (AlgebraData.bracket x z) =
        AlgebraData.bracket (AlgebraData.bracket x y) z := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub, smul_smul,
    mul_sub, sub_mul, mul_assoc]
  module
lemma bracket_trace_skew (x y z : ColorMatrix N) :
    Matrix.trace (AlgebraData.bracket x y * z) =
      -Matrix.trace (y * AlgebraData.bracket x z) := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
    Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
  have hcy : Matrix.trace (x*y*z) = Matrix.trace (y*(z*x)) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, mul_assoc]
  rw [hcy, mul_assoc]
  ring

lemma colorLie_add_left (a b c : ColorVector N) :
    M.colorLie (a+b) c = M.colorLie a c + M.colorLie b c := by
  apply M.colorEmbed_injective
  simp only [M.colorEmbed_lie,map_add,bracket_add_left]
lemma colorLie_add_right (a b c : ColorVector N) :
    M.colorLie a (b+c) = M.colorLie a b + M.colorLie a c := by
  apply M.colorEmbed_injective
  simp only [M.colorEmbed_lie,map_add,bracket_add_right]
lemma colorLie_smul_left (r : ℝ) (a b : ColorVector N) :
    M.colorLie (r • a) b = r • M.colorLie a b := by
  apply M.colorEmbed_injective
  simp only [M.colorEmbed_lie,map_smul,bracket_real_smul_left]
lemma colorLie_smul_right (r : ℝ) (a b : ColorVector N) :
    M.colorLie a (r • b) = r • M.colorLie a b := by
  apply M.colorEmbed_injective
  simp only [M.colorEmbed_lie,map_smul,bracket_real_smul_right]
lemma colorLie_swap (a b : ColorVector N) : M.colorLie a b = -M.colorLie b a := by
  apply M.colorEmbed_injective
  simp only [M.colorEmbed_lie,map_neg]
  exact bracket_neg_swap _ _
lemma colorLie_jacobi (a b c : ColorVector N) :
    M.colorLie a (M.colorLie b c) - M.colorLie b (M.colorLie a c) =
      M.colorLie (M.colorLie a b) c := by
  apply M.colorEmbed_injective
  simp only [M.colorEmbed_lie,map_sub,bracket_jacobi]
lemma colorLie_skew (a b c : ColorVector N) :
    inner ℝ (M.colorLie a b) c = -inner ℝ b (M.colorLie a c) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, M.colorEmbed_inner, M.colorEmbed_inner, M.colorEmbed_lie,
    M.colorEmbed_lie]
  exact bracket_trace_skew _ _ _

def colorAd (a : ColorVector N) : ColorVector N →ₗ[ℝ] ColorVector N where
  toFun := M.colorLie a
  map_add' := M.colorLie_add_right a
  map_smul' r b := M.colorLie_smul_right r a b

lemma colorAd_skew (a : ColorVector N) (b c : ColorVector N) :
    inner ℝ (M.colorAd a b) c = -inner ℝ b (M.colorAd a c) := M.colorLie_skew a b c

lemma colorAd_commutator (a b c : ColorVector N) :
    M.colorAd a (M.colorAd b c) - M.colorAd b (M.colorAd a c) =
      M.colorAd (M.colorLie a b) c := M.colorLie_jacobi a b c

end AlgebraData
end
end BFSSQuantum

end OAI
