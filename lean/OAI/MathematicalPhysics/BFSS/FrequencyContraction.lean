import Mathlib
import OAI.MathematicalPhysics.BFSS.PotentialLimits

namespace OAI

/-! Kinetic-mass and color contractions for the literal fermion field. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
variable {N : ℕ} (M : AlgebraData N)

lemma kineticComplexSymbol_sum (α : SpinIndex) (i : SpaceIndex) (A : ColorIndex N) :
    M.kineticComplexSymbol α (i,A) =
      ∑ δ : SpinIndex, (M.gamma i α δ : ℂ) • M.theta δ A := by
  simp only [kineticComplexSymbol,principalSymbol,cliffordLinear,Fintype.sum_prod_type,
    M.principalCoefficients_coordinate]
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.sum_eq_single A]
  · simp
  · intro B _ hBA
    simp only [ite_eq_right (Ne.symm hBA),Complex.ofReal_zero]
    exact zero_smul ℂ (M.theta β B)
  · simp

lemma kinetic_matrix_contraction (i : SpaceIndex) (A B : ColorIndex N)
    (C : GammaMatrix) :
    (∑ α : SpinIndex, M.kineticComplexSymbol α (i,A) *
      (∑ β : SpinIndex, (C β α : ℂ) • M.theta β B)) =
    ∑ δ : SpinIndex, ∑ β : SpinIndex,
      ((C * M.gamma i) β δ : ℂ) • (M.theta δ A * M.theta β B) := by
  simp only [M.kineticComplexSymbol_sum,Finset.sum_mul,Finset.mul_sum,
    smul_mul_assoc,mul_smul_comm,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro β
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro β _
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply,Complex.ofReal_sum,Complex.ofReal_mul]

lemma gamma_mass_contraction :
    (∑ i : SpaceIndex, BFSSGamma.massWeight i •
      (M.gamma i * BFSSGamma.massT M.gamma * M.gamma i)) =
      (12 : ℝ) • BFSSGamma.massT M.gamma := by
  have hs : (∑ i ∈ BFSSGamma.firstThree, BFSSGamma.massWeight i) = (6 : ℝ) := by
    rw [BFSSGamma.firstThree,
      Finset.sum_insert (by decide : (0 : Fin 9) ∉ ({1,2} : Finset (Fin 9))),
      Finset.sum_insert (by decide : (1 : Fin 9) ∉ ({2} : Finset (Fin 9))),
      Finset.sum_singleton]
    norm_num [BFSSGamma.massWeight,Fin.lt_def]
  rw [← BFSSGamma.word_firstThree, BFSSGamma.weighted_word_conj M.gamma M.gamma_clifford,
    BFSSGamma.firstThree_card,hs]
  norm_num

lemma massLinear_single (α : SpinIndex) (i : SpaceIndex) (A : ColorIndex N) :
    M.massLinear α (EuclideanSpace.single (i,A) 1) =
      (∑ β : SpinIndex,
        ((BFSSGamma.massWeight i * (M.gamma i * BFSSGamma.massT M.gamma) β α : ℝ) : ℂ) •
          M.theta β A).restrictScalars ℝ := by
  have hh : M.massLinear α (EuclideanSpace.single (i,A) 1) =
      ∑ β : SpinIndex, (BFSSGamma.massWeight i * (M.gamma i * BFSSGamma.massT M.gamma) β α) •
        (M.theta β A).restrictScalars ℝ := by
    simp only [massLinear,_root_.sum_apply,ContinuousLinearMap.smulRight_apply]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.sum_eq_single A]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Prod.mk.injEq,Ne.symm hji]
      · simp
    · intro B _ hBA
      apply Finset.sum_eq_zero
      intro j _
      simp [Prod.mk.injEq,Ne.symm hBA]
    · simp
  rw [hh]
  apply ContinuousLinearMap.ext
  intro z
  simp only [_root_.sum_apply,IsSMulApply.smul_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rfl

lemma kinetic_mass_contraction (A : ColorIndex N) :
    (∑ i : SpaceIndex, ∑ α : SpinIndex, M.kineticComplexSymbol α (i,A) *
      (∑ β : SpinIndex,
        ((BFSSGamma.massWeight i * (M.gamma i * BFSSGamma.massT M.gamma) β α : ℝ) : ℂ) •
          M.theta β A)) =
    ∑ δ : SpinIndex, ∑ β : SpinIndex,
      ((12 * BFSSGamma.massT M.gamma β δ : ℝ) : ℂ) •
        (M.theta δ A * M.theta β A) := by
  have hc (i : SpaceIndex) := M.kinetic_matrix_contraction i A A
    (BFSSGamma.massWeight i • (M.gamma i * BFSSGamma.massT M.gamma))
  simp only [Matrix.smul_apply,smul_eq_mul] at hc
  simp_rw [hc,smul_mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  rw [← Finset.sum_smul,← Complex.ofReal_sum]
  congr 2
  have hh := congrArg (fun C : GammaMatrix => C β δ) M.gamma_mass_contraction
  simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using hh

lemma deformedFermionField_mass (x : Boson N) :
    M.deformedFermionField 0 1 x =
      (((3/4 : ℂ) * Complex.I) •
        (∑ A : ColorIndex N, ∑ δ : SpinIndex, ∑ β : SpinIndex,
          (BFSSGamma.massT M.gamma δ β : ℂ) •
            (M.theta δ A * M.theta β A))).restrictScalars ℝ := by
  let R := ContinuousLinearMap.restrictScalarsₗ ℂ (Fermion N) (Fermion N) ℝ ℂ
  let P (i : SpaceIndex) (A : ColorIndex N) (α : SpinIndex) :=
    M.kineticComplexSymbol α (i,A) *
      (∑ β : SpinIndex,
        ((BFSSGamma.massWeight i * (M.gamma i * BFSSGamma.massT M.gamma) β α : ℝ) : ℂ) •
          M.theta β A)
  have ht (α : SpinIndex) (i : SpaceIndex) (A : ColorIndex N) :
      M.kineticSkewSymbol α (i,A) * M.massLinear α (EuclideanSpace.single (i,A) 1) =
        R ((-Complex.I) • P i A α) := by
    rw [M.massLinear_single]
    apply ContinuousLinearMap.ext
    intro z
    simp only [kineticSkewSymbol,mul_apply_eq_comp,
      IsSMulApply.smul_apply,ContinuousLinearMap.coe_restrictScalars']
    rfl
  have hs : (∑ α : SpinIndex, ∑ p : SpaceIndex × ColorIndex N,
      M.kineticSkewSymbol α p * M.massLinear α (EuclideanSpace.single p 1)) =
      R ((-Complex.I) • (∑ A : ColorIndex N, ∑ i : SpaceIndex, ∑ α : SpinIndex, P i A α)) := by
    simp only [Fintype.sum_prod_type,ht]
    have he : (∑ α : SpinIndex, ∑ i : SpaceIndex, ∑ A : ColorIndex N, R ((-Complex.I) • P i A α)) =
        ∑ A : ColorIndex N, ∑ i : SpaceIndex, ∑ α : SpinIndex, R ((-Complex.I) • P i A α) := by
      rw [Finset.sum_comm]
      conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    rw [he]
    simp only [Finset.smul_sum,map_sum]
  have hc : (∑ A : ColorIndex N, ∑ i : SpaceIndex, ∑ α : SpinIndex, P i A α) =
      (-12 : ℂ) • (∑ A : ColorIndex N, ∑ δ : SpinIndex, ∑ β : SpinIndex,
        (BFSSGamma.massT M.gamma δ β : ℂ) • (M.theta δ A * M.theta β A)) := by
    have hT := BFSSGamma.massT_transpose M.gamma M.gamma_clifford M.gamma_symmetric
    have hTe (β δ : SpinIndex) : BFSSGamma.massT M.gamma β δ = -BFSSGamma.massT M.gamma δ β :=
      congrArg (fun C : GammaMatrix => C δ β) hT
    simp only [P]
    simp_rw [M.kinetic_mass_contraction]
    simp only [Complex.ofReal_mul,
      Complex.ofReal_ofNat,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro δ _
    apply Finset.sum_congr rfl
    intro β _
    rw [hTe β δ,Complex.ofReal_neg]
    congr 1
    ring
  have hd (α : SpinIndex) (p : SpaceIndex × ColorIndex N) :
      fderiv ℝ (M.deformedRealField 0 1 α) x (EuclideanSpace.single p 1) =
        M.massLinear α (EuclideanSpace.single p 1) := by
    rw [M.deformedRealField_fderiv]
    module
  unfold deformedFermionField MixedEnergy.remainderField
  simp only [hd]
  rw [hs,hc,smul_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),← map_smul]
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  change R (((1/16 : ℝ) : ℂ) • (((-Complex.I) * (-12)) • _)) = R _
  congr 1
  rw [smul_smul]
  congr 1
  norm_num
  ring

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def spinColumn (C : GammaMatrix) (α : SpinIndex) (A : ColorIndex N) :
    Fermion N →L[ℂ] Fermion N := ∑ β : SpinIndex, (C β α : ℂ) • M.theta β A

lemma sum_rotate_five {ι κ ξ μ ν W : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
    [Fintype μ] [Fintype ν] [AddCommMonoid W] (f : ι → κ → ξ → μ → ν → W) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, f i j k l m) =
      ∑ j, ∑ k, ∑ l, ∑ m, ∑ i, f i j k l m := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

lemma bracketBilinear_restrict (α : SpinIndex) (x y : Boson N) :
    M.bracketBilinear α x y =
      (∑ A : ColorIndex N, ∑ p : SpatialPair, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
        ((-M.structureConstant A B C * x (p.1.1,B) * y (p.1.2,C) : ℝ) : ℂ) •
          M.spinColumn (BFSSGamma.pairGamma M.gamma p) α A).restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [bracketBilinear,spinColumn,_root_.sum_apply,
    ContinuousLinearMap.smulRight_apply,EuclideanSpace.coe_proj,
    ContinuousLinearMap.coe_restrictScalars',IsSMulApply.smul_apply,
    Finset.smul_sum,smul_smul]
  rw [sum_rotate_five]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro β _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  congr 1
  change ((x (p.1.1,B) * (y (p.1.2,C) *
    (-M.structureConstant A B C * BFSSGamma.pairGamma M.gamma p β α)) : ℝ) : ℂ) =
    -(M.structureConstant A B C : ℂ) * (x (p.1.1,B) : ℂ) * (y (p.1.2,C) : ℂ) *
      (BFSSGamma.pairGamma M.gamma p β α : ℂ)
  push_cast
  ring

lemma structureConstant_cycle (A B C : ColorIndex N) :
    M.structureConstant A B C = M.structureConstant B C A := by
  have ht := bracket_trace_skew (M.color C) (M.color A) (M.color B)
  have hs : AlgebraData.bracket (M.color C) (M.color B) =
      -AlgebraData.bracket (M.color B) (M.color C) := bracket_neg_swap _ _
  rw [hs,mul_neg,Matrix.trace_neg,neg_neg,Matrix.trace_mul_comm] at ht
  exact (congrArg Complex.re ht).symm

lemma structureConstant_swap (A B C : ColorIndex N) :
    M.structureConstant A C B = -M.structureConstant A B C := by
  unfold structureConstant
  rw [bracket_neg_swap (M.color C) (M.color B),mul_neg,Matrix.trace_neg,Complex.neg_re]

end
end BFSSQuantum.AlgebraData

end OAI
