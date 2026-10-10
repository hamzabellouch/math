import Mathlib
import OAI.MathematicalPhysics.BFSS.DeformedCharge

namespace OAI

/-! Fermion multiplier growth and global deformed potential scaling. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset Matrix
variable {N : ℕ} (M : AlgebraData N)

local instance potentialBoundsDerivativeOperatorNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance potentialBoundsDerivativeOperatorNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance potentialBoundsDerivativeFieldNormedAddCommGroup :
    NormedAddCommGroup (Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N)) := inferInstance
local instance potentialBoundsDerivativeFieldNormedSpace :
    NormedSpace ℝ (Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N)) := inferInstance

def bracketBilinear (α : SpinIndex) :
    Boson N →L[ℝ] Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N) :=
  ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ p : SpatialPair,
    ∑ B : ColorIndex N, ∑ C : ColorIndex N,
      (EuclideanSpace.proj (𝕜 := ℝ) (p.1.1,B)).smulRight
        ((EuclideanSpace.proj (𝕜 := ℝ) (p.1.2,C)).smulRight
          ((-M.structureConstant A B C * BFSSGamma.pairGamma M.gamma p β α) •
            (M.theta β A).restrictScalars ℝ))

def massLinear (α : SpinIndex) : Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N) :=
  ∑ β : SpinIndex, ∑ A : ColorIndex N, ∑ i : SpaceIndex,
    (EuclideanSpace.proj (𝕜 := ℝ) (i,A)).smulRight
      ((BFSSGamma.massWeight i * (M.gamma i * BFSSGamma.massT M.gamma) β α) •
        (M.theta β A).restrictScalars ℝ)

lemma deformedRealField_polarized (h m : ℝ) (α : SpinIndex) (x : Boson N) :
    M.deformedRealField h m α x = h • M.bracketBilinear α x x + m • M.massLinear α x := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [deformedRealField, deformedPotentialMultiplier, cliffordLinear,
    deformedPotentialCoefficients, deformedPotentialMatrix, BFSSGamma.bracketMassMatrix,
    coordinateBracket, bracketBilinear, massLinear, Fintype.sum_prod_type,
    ContinuousLinearMap.coe_restrictScalars', _root_.sum_apply, _root_.smul_apply,
    _root_.add_apply, ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
    Finset.sum_smul, Finset.smul_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_neg, Finset.sum_smul, add_smul,
    Finset.sum_add_distrib, smul_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro B _
    apply Finset.sum_congr rfl
    intro C _
    module
  · apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro i _
    module

lemma deformedRealField_derivative_bound (h m : ℝ) (α : SpinIndex) (x v : Boson N) :
    ‖fderiv ℝ (M.deformedRealField h m α) x v‖ ≤
      (2*|h| *‖M.bracketBilinear α‖*‖x‖ + |m| *‖M.massLinear α‖)*‖v‖ := by
  have he : M.deformedRealField h m α = fun y => h • M.bracketBilinear α y y + m • M.massLinear α y :=
    funext (M.deformedRealField_polarized h m α)
  rw [he]
  exact BilinearGrowth.derivative_quadratic_linear_bound _ _ _ _ _ _

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset Matrix
variable {N : ℕ} (M : AlgebraData N)

local instance potentialBoundsGrowthOperatorNormedAddCommGroup :
    NormedAddCommGroup (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance potentialBoundsGrowthOperatorNormedSpace :
    NormedSpace ℝ (Fermion N →L[ℝ] Fermion N) := inferInstance
local instance potentialBoundsGrowthFieldNormedAddCommGroup :
    NormedAddCommGroup (Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N)) := inferInstance
local instance potentialBoundsGrowthFieldNormedSpace :
    NormedSpace ℝ (Boson N →L[ℝ] (Fermion N →L[ℝ] Fermion N)) := inferInstance

def fermionGrowthConstant : ℝ :=
  (1/16 : ℝ) * ∑ α : SpinIndex, ∑ p : SpaceIndex × ColorIndex N,
    ‖M.kineticSkewSymbol α p‖ * (2*‖M.bracketBilinear α‖ + ‖M.massLinear α‖)

lemma fermionGrowthConstant_nonneg : 0 ≤ M.fermionGrowthConstant := by
  unfold fermionGrowthConstant
  positivity

lemma deformedFermionField_growth (h m : ℝ) (x : Boson N) :
    ‖M.deformedFermionField h m x‖ ≤ M.fermionGrowthConstant * (|h| * ‖x‖ + |m|) := by
  have hp (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
      ‖M.kineticSkewSymbol α p * fderiv ℝ (M.deformedRealField h m α) x
          (EuclideanSpace.single p 1)‖ ≤
      (‖M.kineticSkewSymbol α p‖ * (2*‖M.bracketBilinear α‖ + ‖M.massLinear α‖)) *
        (|h| * ‖x‖ + |m|) := by
    have hd := M.deformedRealField_derivative_bound h m α x (EuclideanSpace.single p 1)
    simp only [PiLp.norm_single, norm_one, mul_one] at hd
    calc
      _ ≤ ‖M.kineticSkewSymbol α p‖ *
          ‖fderiv ℝ (M.deformedRealField h m α) x (EuclideanSpace.single p 1)‖ := norm_mul_le _ _
      _ ≤ ‖M.kineticSkewSymbol α p‖ *
          (2*|h| * ‖M.bracketBilinear α‖*‖x‖ + |m| * ‖M.massLinear α‖) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ ‖M.kineticSkewSymbol α p‖ *
          ((2*‖M.bracketBilinear α‖ + ‖M.massLinear α‖) * (|h| * ‖x‖ + |m|)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        nlinarith [mul_nonneg (norm_nonneg (M.massLinear α)) (mul_nonneg (abs_nonneg h) (norm_nonneg x)),
          mul_nonneg (norm_nonneg (M.bracketBilinear α)) (abs_nonneg m)]
      _ = _ := by ring
  unfold deformedFermionField MixedEnergy.remainderField fermionGrowthConstant
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/16)]
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro α _
  rw [Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => hp α p))

lemma deformedFermionField_inner_lower (h m : ℝ) (x : Boson N) (z : Fermion N) :
    -(M.fermionGrowthConstant * (|h| * ‖x‖ + |m|)) * ‖z‖^2 ≤
      inner ℝ z (M.deformedFermionField h m x z) := by
  have hc := M.deformedFermionField_growth h m x
  have hz := (M.deformedFermionField h m x).le_opNorm z
  have hi := neg_le_abs (inner ℝ z (M.deformedFermionField h m x z))
  have hi' := abs_real_inner_le_norm z (M.deformedFermionField h m x z)
  have hh : ‖z‖ * ‖M.deformedFermionField h m x z‖ ≤
      (M.fermionGrowthConstant * (|h| * ‖x‖ + |m|)) * ‖z‖^2 := by
    calc
      _ ≤ ‖z‖ * ((M.fermionGrowthConstant * (|h| * ‖x‖ + |m|)) * ‖z‖) := by
        gcongr
        exact hz.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg z))
      _ = _ := by ring
  linarith

end
end BFSSQuantum.AlgebraData

namespace BFSS
noncomputable section

def scaleConfiguration {N : ℕ} (r : ℝ) (x : Configuration N) : Configuration N :=
  fun i => ⟨r • (x i).val, (x i).property.1.smul (IsSelfAdjoint.all r),
    by simp only [Matrix.trace_smul, (x i).property.2, smul_zero]⟩

lemma configurationNormSq_scale {N : ℕ} (r : ℝ) (x : Configuration N) :
    configurationNormSq (scaleConfiguration r x) = r ^ 2 * configurationNormSq x := by
  simp only [configurationNormSq, scaleConfiguration, hsNormSq_real_smul, Finset.mul_sum]

lemma massive_potential_scaling {N : ℕ} (h m : ℝ) (hh : 0 < h) (hm : 0 < m)
    (x : Configuration N) :
    massivePotential h m x = (m ^ 4 / h ^ 2) *
      massivePotential 1 1 (scaleConfiguration (h / m) x) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hres (a b c : Mat N) :
      realBracket ((h / m) • a) ((h / m) • b) - (2 : ℝ) • ((h / m) • c) =
      (h / m ^ 2) • ((h : ℂ) • realBracket a b - (2 * m : ℝ) • c) := by
    rw [realBracket_real_smul, smul_sub, smul_smul]
    congr 1
    · ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_pow]
      field_simp
    · rw [smul_smul]
      congr 1
      field_simp
  dsimp only [massivePotential, scaleConfiguration]
  unfold Configuration Color at x
  simp only [one_pow, one_mul, mul_one, Complex.ofReal_one, one_smul]
  rw [hres, hres, hres]
  simp only [realBracket_real_smul, hsNormSq_real_smul]
  have hsum : (∑ i : Fin 9, ∑ j : Fin 9,
      if i < j ∧ 3 ≤ j.val then ((h / m) ^ 2) ^ 2 * hsNormSq
        (realBracket (x i).val (x j).val) else 0) =
      ((h / m) ^ 2) ^ 2 * (∑ i : Fin 9, ∑ j : Fin 9,
      if i < j ∧ 3 ≤ j.val then hsNormSq
        (realBracket (x i).val (x j).val) else 0) := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  have hsum2 : (∑ i : Fin 9,
      if 3 ≤ i.val then (h / m) ^ 2 * hsNormSq (x i).val else 0) =
      (h / m) ^ 2 * (∑ i : Fin 9, if 3 ≤ i.val then hsNormSq (x i).val else 0) := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [hsum, hsum2]
  field_simp

end
end BFSS

namespace BFSSQuantum.AlgebraData
noncomputable section
open Finset Matrix
variable {N : ℕ} (M : AlgebraData N)

lemma matrixConfiguration_smul (r : ℝ) (x : Boson N) :
    M.matrixConfiguration (r • x) = BFSS.scaleConfiguration r (M.matrixConfiguration x) := by
  funext i
  apply Subtype.ext
  change M.colorCombination (fun A => r * x (i,A)) = r • M.colorCombination (fun A => x (i,A))
  rw [M.colorCombination_smul]
  ext a b
  simp

lemma deformedBosonicPotential_scaling (h m : ℝ) (hh : 0 < h) (hm : 0 < m) (x : Boson N) :
    M.deformedBosonicPotential h m x = (m^4 / h^2) *
      M.deformedBosonicPotential 1 1 ((h/m) • x) := by
  simp only [M.deformedBosonicPotential_matrix, M.matrixConfiguration_smul]
  exact BFSS.massive_potential_scaling h m hh hm _

lemma deformedBosonicPotential_nonneg (h m : ℝ) (x : Boson N) :
    0 ≤ M.deformedBosonicPotential h m x := by
  unfold deformedBosonicPotential
  positivity

theorem deformedBosonicPotential_global (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ h m : ℝ, 0 < h → 0 < m →
      ∀ x : Boson N, c*m^2*‖x‖^2 - C*(m^4/h^2) ≤ M.deformedBosonicPotential h m x := by
  obtain ⟨c,hc,R,hR⟩ := M.deformedBosonicPotential_coercive hN
  let K : ℝ := max R 0
  have hK : 0 ≤ K := le_max_right _ _
  have hbase (x : Boson N) : c*‖x‖^2 - c*K^2 ≤ M.deformedBosonicPotential 1 1 x := by
    by_cases hx : R ≤ ‖x‖
    · exact (sub_le_self _ (mul_nonneg hc.le (sq_nonneg K))).trans (hR x hx)
    · have hxr : ‖x‖ ≤ K := (le_of_not_ge hx).trans (le_max_left _ _)
      have hs : ‖x‖^2 ≤ K^2 := pow_le_pow_left₀ (norm_nonneg _) hxr 2
      have hcs := mul_le_mul_of_nonneg_left hs hc.le
      exact (sub_nonpos.mpr hcs).trans (M.deformedBosonicPotential_nonneg 1 1 x)
  refine ⟨c,hc,c*K^2,mul_nonneg hc.le (sq_nonneg K),?_⟩
  intro h m hh hm x
  have hs := mul_le_mul_of_nonneg_left (hbase ((h/m) • x))
    (show 0 ≤ m^4/h^2 by positivity)
  rw [← M.deformedBosonicPotential_scaling h m hh hm] at hs
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hh hm)] at hs
  have he : (m^4/h^2) * (c*((h/m)*‖x‖)^2 - c*K^2) =
      c*m^2*‖x‖^2 - c*K^2*(m^4/h^2) := by
    field_simp [ne_of_gt hh, ne_of_gt hm]
  rw [he] at hs
  exact hs

end
end BFSSQuantum.AlgebraData

end OAI
