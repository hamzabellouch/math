import Mathlib
import OAI.MathematicalPhysics.BFSS.FermionFrequency
import OAI.MathematicalPhysics.BFSS.FrequencyContraction

namespace OAI

/-! Quadratic Clifford quantization of the deformed fermion multiplier. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def bracketComplex (α : SpinIndex) (x y : Boson N) : Fermion N →L[ℂ] Fermion N :=
  ∑ A : ColorIndex N, ∑ p : SpatialPair, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
    ((-M.structureConstant A B C * x (p.1.1,B) * y (p.1.2,C) : ℝ) : ℂ) •
      M.spinColumn (BFSSGamma.pairGamma M.gamma p) α A

lemma bracketComplex_restrict (α : SpinIndex) (x y : Boson N) :
    (M.bracketComplex α x y).restrictScalars ℝ = M.bracketBilinear α x y :=
  (M.bracketBilinear_restrict α x y).symm

lemma coordinate_single_contraction {W : Type*} [AddCommGroup W] [Module ℂ W]
    (r : SpaceIndex × ColorIndex N) (F : SpaceIndex × ColorIndex N → W) :
    (∑ k : SpaceIndex × ColorIndex N,
      ((EuclideanSpace.single k (1:ℝ) r : ℝ) : ℂ) • F k) = F r := by
  rw [Finset.sum_eq_single r]
  · simp
  · intro k _ hkr
    have hz : EuclideanSpace.single k (1:ℝ) r = 0 := by
      simp [Ne.symm hkr]
    rw [hz,Complex.ofReal_zero,zero_smul]
  · simp

lemma kinetic_bracket_right (α : SpinIndex) (x : Boson N) :
    (∑ k : SpaceIndex × ColorIndex N,
      M.kineticComplexSymbol α k * M.bracketComplex α x (EuclideanSpace.single k 1)) =
      ∑ A : ColorIndex N, ∑ p : SpatialPair, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
        ((-M.structureConstant A B C * x (p.1.1,B) : ℝ) : ℂ) •
          (M.kineticComplexSymbol α (p.1.2,C) *
            M.spinColumn (BFSSGamma.pairGamma M.gamma p) α A) := by
  simp only [bracketComplex,Finset.mul_sum,mul_smul_comm]
  rw [sum_rotate_five]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  simp only [Complex.ofReal_mul,mul_smul]
  rw [← Finset.smul_sum,← Finset.smul_sum]
  congr 1
  congr 1
  exact coordinate_single_contraction (p.1.2,C) _

lemma kinetic_bracket_left (α : SpinIndex) (x : Boson N) :
    (∑ k : SpaceIndex × ColorIndex N,
      M.kineticComplexSymbol α k * M.bracketComplex α (EuclideanSpace.single k 1) x) =
      ∑ A : ColorIndex N, ∑ p : SpatialPair, ∑ B : ColorIndex N, ∑ C : ColorIndex N,
        ((-M.structureConstant A B C * x (p.1.2,C) : ℝ) : ℂ) •
          (M.kineticComplexSymbol α (p.1.1,B) *
            M.spinColumn (BFSSGamma.pairGamma M.gamma p) α A) := by
  simp only [bracketComplex,Finset.mul_sum,mul_smul_comm]
  rw [sum_rotate_five]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  simp only [mul_right_comm (-M.structureConstant A B C) _ (x (p.1.2,C)),
    Complex.ofReal_mul,mul_smul]
  rw [← Finset.smul_sum,← Finset.smul_sum]
  congr 1
  congr 1
  exact coordinate_single_contraction (p.1.1,B) _

lemma kinetic_pairGamma_first (p : SpatialPair) (A B : ColorIndex N) :
    (∑ α : SpinIndex, M.kineticComplexSymbol α (p.1.1,A) *
      M.spinColumn (BFSSGamma.pairGamma M.gamma p) α B) =
    ∑ δ : SpinIndex, ∑ β : SpinIndex,
      (-M.gamma p.1.2 β δ : ℂ) • (M.theta δ A * M.theta β B) := by
  have h := M.kinetic_matrix_contraction p.1.1 A B (BFSSGamma.pairGamma M.gamma p)
  have hp : BFSSGamma.pairGamma M.gamma p*M.gamma p.1.1 = -M.gamma p.1.2 := by
    rw [BFSSGamma.pairGamma,mul_assoc,BFSSGamma.gamma_anti M.gamma M.gamma_clifford p.2.ne.symm,
      mul_neg,←mul_assoc,BFSSGamma.gamma_sq M.gamma M.gamma_clifford,one_mul]
  simpa only [spinColumn,hp,Matrix.neg_apply,Complex.ofReal_neg] using h

lemma kinetic_pairGamma_second (p : SpatialPair) (A B : ColorIndex N) :
    (∑ α : SpinIndex, M.kineticComplexSymbol α (p.1.2,A) *
      M.spinColumn (BFSSGamma.pairGamma M.gamma p) α B) =
    ∑ δ : SpinIndex, ∑ β : SpinIndex,
      (M.gamma p.1.1 β δ : ℂ) • (M.theta δ A * M.theta β B) := by
  have h := M.kinetic_matrix_contraction p.1.2 A B (BFSSGamma.pairGamma M.gamma p)
  have hp : BFSSGamma.pairGamma M.gamma p*M.gamma p.1.2 = M.gamma p.1.1 := by
    rw [BFSSGamma.pairGamma,mul_assoc,BFSSGamma.gamma_sq M.gamma M.gamma_clifford,mul_one]
  simpa only [spinColumn,hp] using h

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def cubicFermionComponent (x : Boson N) (A : ColorIndex N) (j : SpaceIndex) :
    Fermion N →L[ℂ] Fermion N :=
  ∑ B : ColorIndex N, ∑ C : ColorIndex N,
    ((M.structureConstant A B C * x (j,C) : ℝ) : ℂ) •
      (∑ δ : SpinIndex, ∑ β : SpinIndex,
        (M.gamma j β δ : ℂ) • (M.theta δ B * M.theta β A))

lemma kinetic_bracket_average_right (x : Boson N) :
    (∑ α : SpinIndex, ∑ k : SpaceIndex × ColorIndex N,
      M.kineticComplexSymbol α k * M.bracketComplex α x (EuclideanSpace.single k 1)) =
      ∑ A : ColorIndex N, ∑ p : SpatialPair, M.cubicFermionComponent x A p.1.1 := by
  simp_rw [M.kinetic_bracket_right]
  rw [sum_rotate_five]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [←Finset.smul_sum,M.kinetic_pairGamma_second]
  rw [Finset.sum_comm]
  unfold cubicFermionComponent
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  rw [M.structureConstant_swap A B C,neg_neg]

lemma kinetic_bracket_average_left (x : Boson N) :
    (∑ α : SpinIndex, ∑ k : SpaceIndex × ColorIndex N,
      M.kineticComplexSymbol α k * M.bracketComplex α (EuclideanSpace.single k 1) x) =
      ∑ A : ColorIndex N, ∑ p : SpatialPair, M.cubicFermionComponent x A p.1.2 := by
  simp_rw [M.kinetic_bracket_left]
  rw [sum_rotate_five]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [←Finset.smul_sum,M.kinetic_pairGamma_first]
  simp only [cubicFermionComponent,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  change ((-M.structureConstant A B C*x (p.1.2,C) : ℝ) : ℂ) *
    (-(M.gamma p.1.2 β δ : ℂ)) =
    ((M.structureConstant A B C*x (p.1.2,C) : ℝ) : ℂ) * (M.gamma p.1.2 β δ : ℂ)
  push_cast
  ring

lemma kinetic_bracket_average (x : Boson N) :
    (∑ α : SpinIndex, ∑ k : SpaceIndex × ColorIndex N,
      M.kineticComplexSymbol α k *
        (M.bracketComplex α x (EuclideanSpace.single k 1) +
        M.bracketComplex α (EuclideanSpace.single k 1) x)) =
      (8 : ℂ) • ∑ j : SpaceIndex, ∑ A : ColorIndex N, M.cubicFermionComponent x A j := by
  simp only [mul_add,Finset.sum_add_distrib]
  rw [M.kinetic_bracket_average_right,M.kinetic_bracket_average_left,
    ←Finset.sum_add_distrib]
  simp_rw [←Finset.sum_add_distrib,BFSSPairSum.endpoints]
  rw [←Finset.smul_sum,Finset.sum_comm]
  simpa only [Nat.cast_ofNat] using
    (Nat.cast_smul_eq_nsmul ℂ 8 (∑ j : SpaceIndex, ∑ A : ColorIndex N,
      M.cubicFermionComponent x A j)).symm

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

lemma deformedFermionField_linear_parameters (h m : ℝ) (x : Boson N) :
    M.deformedFermionField h m x =
      h • M.deformedFermionField 1 0 x + m • M.deformedFermionField 0 1 x := by
  simp only [deformedFermionField,MixedEnergy.remainderField,M.deformedRealField_fderiv,
    one_smul,zero_smul,zero_add,add_zero,mul_add,mul_smul_comm,
    Finset.sum_add_distrib,←Finset.smul_sum,smul_add,smul_smul]
  module

lemma deformedFermionField_bracket (x : Boson N) :
    M.deformedFermionField 1 0 x =
      (((-Complex.I)/2) •
        (∑ j : SpaceIndex, ∑ A : ColorIndex N, M.cubicFermionComponent x A j)).restrictScalars ℝ := by
  let R := ContinuousLinearMap.restrictScalarsₗ ℂ (Fermion N) (Fermion N) ℝ ℂ
  let P (α : SpinIndex) (k : SpaceIndex × ColorIndex N) :=
    M.kineticComplexSymbol α k *
      (M.bracketComplex α x (EuclideanSpace.single k 1) +
        M.bracketComplex α (EuclideanSpace.single k 1) x)
  have ht (α : SpinIndex) (k : SpaceIndex × ColorIndex N) :
      M.kineticSkewSymbol α k *
          (M.bracketBilinear α x (EuclideanSpace.single k 1) +
            M.bracketBilinear α (EuclideanSpace.single k 1) x) =
        R ((-Complex.I) • P α k) := by
    rw [←M.bracketComplex_restrict,←M.bracketComplex_restrict]
    apply ContinuousLinearMap.ext
    intro z
    simp only [kineticSkewSymbol,mul_apply_eq_comp,
      IsAddApply.add_apply,IsSMulApply.smul_apply,
      ContinuousLinearMap.coe_restrictScalars']
    rfl
  have hs : (∑ α : SpinIndex, ∑ k : SpaceIndex × ColorIndex N, P α k) =
      (8:ℂ) • ∑ j : SpaceIndex, ∑ A : ColorIndex N, M.cubicFermionComponent x A j :=
    M.kinetic_bracket_average x
  have hd (α : SpinIndex) (k : SpaceIndex × ColorIndex N) :
      fderiv ℝ (M.deformedRealField 1 0 α) x (EuclideanSpace.single k 1) =
        M.bracketBilinear α x (EuclideanSpace.single k 1) +
        M.bracketBilinear α (EuclideanSpace.single k 1) x := by
    rw [M.deformedRealField_fderiv]
    module
  unfold deformedFermionField MixedEnergy.remainderField
  simp only [hd,ht,←map_sum,←Finset.smul_sum]
  rw [hs,smul_smul]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),← map_smul]
  change R (((1/16 : ℝ) : ℂ) • (((-Complex.I) * 8) • _)) = R _
  congr 1
  rw [smul_smul]
  congr 1
  norm_num
  ring

def fermionCoefficient (x : Boson N) : FrequencyMatrix N :=
  fun r s => (if r.2 = s.2 then (3/2:ℝ) * BFSSGamma.massT M.gamma r.1 s.1 else 0) -
    ∑ j : SpaceIndex, ∑ C : ColorIndex N,
      M.structureConstant s.2 r.2 C * x (j,C) * M.gamma j r.1 s.1

def quantizeFrequency (K : FrequencyMatrix N) : Fermion N →L[ℂ] Fermion N :=
  (Complex.I/2) • ∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
    (K r s : ℂ) • (M.theta r.1 r.2 * M.theta s.1 s.2)

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

lemma sum_rotate_six {ι κ ξ μ ν η W : Type*} [Fintype ι] [Fintype κ] [Fintype ξ]
    [Fintype μ] [Fintype ν] [Fintype η] [AddCommMonoid W]
    (f : ι → κ → ξ → μ → ν → η → W) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ n, f i j k l m n) =
      ∑ j, ∑ k, ∑ l, ∑ m, ∑ n, ∑ i, f i j k l m n := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact sum_rotate_five _

lemma frequency_mass_contraction :
    (∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
      ((if r.2 = s.2 then (3/2:ℝ) * BFSSGamma.massT M.gamma r.1 s.1 else 0 : ℝ) : ℂ) •
        (M.theta r.1 r.2*M.theta s.1 s.2)) =
      (3/2:ℂ) • (∑ A : ColorIndex N, ∑ δ : SpinIndex, ∑ β : SpinIndex,
        (BFSSGamma.massT M.gamma δ β : ℂ) • (M.theta δ A*M.theta β A)) := by
  have hz (T : Fermion N →L[ℂ] Fermion N) : (0:ℂ) • T = 0 := zero_smul ℂ T
  simp only [Fintype.sum_prod_type,apply_ite,Complex.ofReal_zero,ite_smul,hz]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum,smul_smul,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro β _
  rw [Finset.sum_eq_single A]
  · simp
  · intro B _ hBA
    simp only [ite_eq_right (Ne.symm hBA)]
  · simp

lemma frequency_bracket_contraction (x : Boson N) :
    (∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
      ((∑ j : SpaceIndex, ∑ C : ColorIndex N,
        M.structureConstant s.2 r.2 C*x (j,C)*M.gamma j r.1 s.1 : ℝ) : ℂ) •
          (M.theta r.1 r.2*M.theta s.1 s.2)) =
      ∑ j : SpaceIndex, ∑ A : ColorIndex N, M.cubicFermionComponent x A j := by
  have hd (c : SpaceIndex → ColorIndex N → ℂ) (T : Fermion N →L[ℂ] Fermion N) :
      (∑ j, ∑ C, c j C) • T = ∑ j, ∑ C, c j C • T := by
    calc
      _ = ∑ j, (∑ C, c j C) • T := @Finset.sum_smul SpaceIndex ℂ
        (Fermion N →L[ℂ] Fermion N) _ _ _ (fun j => ∑ C, c j C) Finset.univ T
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact @Finset.sum_smul (ColorIndex N) ℂ (Fermion N →L[ℂ] Fermion N)
          _ _ _ (c j) Finset.univ T
  simp only [Fintype.sum_prod_type,Complex.ofReal_sum,hd]
  rw [sum_rotate_six]
  conv_lhs =>
    arg 2
    intro D
    rw [sum_rotate_five]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro A
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [cubicFermionComponent,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro β _
  have hg : M.gamma j δ β = M.gamma j β δ :=
    congrArg (fun K : GammaMatrix => K β δ) (M.gamma_symmetric j).eq
  rw [hg,Complex.ofReal_mul]

theorem deformedFermionField_quantized (x : Boson N) :
    M.deformedFermionField 1 1 x =
      (M.quantizeFrequency (M.fermionCoefficient x)).restrictScalars ℝ := by
  rw [M.deformedFermionField_linear_parameters,M.deformedFermionField_bracket,
    M.deformedFermionField_mass]
  simp only [one_smul]
  have he : M.quantizeFrequency (M.fermionCoefficient x) =
      ((-Complex.I)/2) • (∑ j : SpaceIndex, ∑ A : ColorIndex N, M.cubicFermionComponent x A j) +
      (((3/4 : ℂ) * Complex.I) •
        (∑ A : ColorIndex N, ∑ δ : SpinIndex, ∑ β : SpinIndex,
          (BFSSGamma.massT M.gamma δ β : ℂ) • (M.theta δ A*M.theta β A))) := by
    have hs (a b : ℂ) (T : Fermion N →L[ℂ] Fermion N) :
        (a-b) • T = a • T-b • T := sub_smul a b T
    simp only [quantizeFrequency,fermionCoefficient,Complex.ofReal_sub,hs,
      Finset.sum_sub_distrib]
    rw [M.frequency_mass_contraction,M.frequency_bracket_contraction]
    module
  rw [he]
  rfl

end
end BFSSQuantum.AlgebraData

end OAI
