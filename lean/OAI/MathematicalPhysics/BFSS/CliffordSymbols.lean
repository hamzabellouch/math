import Mathlib
import OAI.MathematicalPhysics.BFSS.Core

namespace OAI

/-! Clifford linear symbols, spin contractions and charge multiplier identities. -/

namespace BFSSQuantum
noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate
namespace AlgebraData
variable {N : ℕ} (M : AlgebraData N)

abbrev FermionIndex (N : ℕ) := SpinIndex × ColorIndex N

def cliffordLinear (a : FermionIndex N → ℝ) : Fermion N →L[ℂ] Fermion N :=
  ∑ p : FermionIndex N, (a p : ℂ) • M.theta p.1 p.2

lemma cliffordLinear_mixed (a b : FermionIndex N → ℝ) :
    M.cliffordLinear a * M.cliffordLinear b + M.cliffordLinear b * M.cliffordLinear a =
      ((∑ p : FermionIndex N, a p * b p : ℝ) : ℂ) •
        (1 : Fermion N →L[ℂ] Fermion N) := by
  unfold cliffordLinear
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  conv_lhs =>
    lhs
    rw [Finset.sum_comm]
  have hab (p q : FermionIndex N) : (b q : ℂ) * (a p : ℂ) = (a p : ℂ) * (b q : ℂ) := mul_comm _ _
  simp_rw [hab]
  rw [← Finset.sum_add_distrib]
  have hpair (p q : FermionIndex N) :
      ((a p : ℂ) * (b q : ℂ)) • (M.theta p.1 p.2 * M.theta q.1 q.2) +
      ((a p : ℂ) * (b q : ℂ)) • (M.theta q.1 q.2 * M.theta p.1 p.2) =
      (if p = q then ((a p : ℂ) * (b p : ℂ)) else 0) • (1 : Fermion N →L[ℂ] Fermion N) := by
    rw [← smul_add ((a p : ℂ) * (b q : ℂ))
      (M.theta p.1 p.2 * M.theta q.1 q.2) (M.theta q.1 q.2 * M.theta p.1 p.2),
      M.theta_CAR]
    by_cases hpq : p = q
    · simp [hpq]
    · have hneq : ¬(p.1 = q.1 ∧ p.2 = q.2) := by simpa only [← Prod.ext_iff] using hpq
      simp [hpq, hneq, zero_smul ℂ (1 : Fermion N →L[ℂ] Fermion N)]
  simp_rw [← Finset.sum_add_distrib, hpair]
  simp only [ite_smul]
  simp only [zero_smul ℂ (1 : Fermion N →L[ℂ] Fermion N),
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  erw [← Finset.sum_smul]
  congr 1
  simp only [← Complex.ofReal_mul, Complex.ofReal_sum]

lemma cliffordLinear_sq (a : FermionIndex N → ℝ) :
    M.cliffordLinear a * M.cliffordLinear a =
      ((1 / 2 : ℝ) * (∑ p : FermionIndex N, a p ^ 2) : ℂ) •
        (1 : Fermion N →L[ℂ] Fermion N) := by
  have h := M.cliffordLinear_mixed a a
  simp only [← sq] at h
  have h' := congrArg (fun L : Fermion N →L[ℂ] Fermion N => (1 / 2 : ℂ) • L) h
  norm_num [smul_add, ← add_smul, smul_smul, pow_two] at h' ⊢
  exact h'

lemma cliffordLinear_selfAdjoint (a : FermionIndex N → ℝ) :
    IsSelfAdjoint (M.cliffordLinear a) := by
  have hs (p : FermionIndex N) : IsSelfAdjoint ((a p : ℂ) • M.theta p.1 p.2) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    change inner ℂ ((a p : ℂ) • M.theta p.1 p.2 x) y =
      inner ℂ x ((a p : ℂ) • M.theta p.1 p.2 y)
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    exact congrArg ((a p : ℂ) * ·) ((M.theta_selfAdjoint p.1 p.2).isSymmetric x y)
  exact isSelfAdjoint_sum (R := Fermion N →L[ℂ] Fermion N) Finset.univ (fun p _ => hs p)

lemma cliffordLinear_norm_sq (a : FermionIndex N → ℝ) (z : Fermion N) :
    ‖M.cliffordLinear a z‖ ^ 2 = (1 / 2 : ℝ) * (∑p, a p ^ 2) * ‖z‖ ^ 2 := by
  have hi := (M.cliffordLinear_selfAdjoint a).isSymmetric z (M.cliffordLinear a z)
  have hh := congrArg (fun L : Fermion N →L[ℂ] Fermion N => L z)
    (M.cliffordLinear_sq a)
  change M.cliffordLinear a (M.cliffordLinear a z) =
    (((1 / 2 : ℝ) : ℂ) * ((∑p, a p ^ 2 : ℝ) : ℂ)) • z at hh
  rw [← Complex.ofReal_mul] at hh
  have hi' : inner ℂ (M.cliffordLinear a z) (M.cliffordLinear a z) =
      inner ℂ z ((((1 / 2 : ℝ) * ∑p, a p ^ 2 : ℝ) : ℂ) • z) :=
    hi.trans (congrArg (inner ℂ z) hh)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi'
  have hr := congrArg Complex.re hi'
  norm_num [← Complex.ofReal_pow, ← Complex.ofReal_mul] at hr
  exact hr

def gammaLinear (a : SpaceIndex → ℝ) : GammaMatrix := ∑i, a i • M.gamma i

lemma gammaLinear_mixed (a b : SpaceIndex → ℝ) :
    M.gammaLinear a * M.gammaLinear b + M.gammaLinear b * M.gammaLinear a =
      (2 * ∑i, a i * b i) • (1 : GammaMatrix) := by
  unfold gammaLinear
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]
  conv_lhs =>
    lhs
    rw [Finset.sum_comm]
  have hab (i j : SpaceIndex) : b j * a i = a i * b j := mul_comm _ _
  simp_rw [hab]
  rw [← Finset.sum_add_distrib]
  have hp (i j : SpaceIndex) :
      (a i * b j) • (M.gamma i * M.gamma j) +
      (a i * b j) • (M.gamma j * M.gamma i) =
      (if i = j then 2 * a i * b i else 0) • (1 : GammaMatrix) := by
    rw [← smul_add, M.gamma_clifford]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, nsmul_eq_mul, mul_one]
      change (a i * b i) • (2 : GammaMatrix) = (2 * a i * b i) • (1 : GammaMatrix)
      rw [show (2 : GammaMatrix) = (1 : GammaMatrix) + 1 by norm_num,
        smul_add, ← add_smul]
      congr 1
      ring
    · simp [hij]
  simp_rw [← Finset.sum_add_distrib, hp]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma gammaLinear_sq (a : SpaceIndex → ℝ) :
    M.gammaLinear a * M.gammaLinear a = (∑i, a i ^ 2) • (1 : GammaMatrix) := by
  have h := M.gammaLinear_mixed a a
  have h' := congrArg (fun L : GammaMatrix => (1 / 2 : ℝ) • L) h
  norm_num [smul_add, ← add_smul, smul_smul, ← pow_two] at h'
  have hc : (1 / 2 : ℝ) * (2 * ∑i, a i ^ 2) = ∑i, a i ^ 2 := by ring
  rw [hc] at h'
  simpa only [pow_two] using h'

lemma gammaLinear_symmetric (a : SpaceIndex → ℝ) : (M.gammaLinear a).IsSymm := by
  change (M.gammaLinear a).transpose = M.gammaLinear a
  unfold gammaLinear
  simp only [Matrix.transpose_sum, Matrix.transpose_smul]
  congr 1
  funext i
  rw [(M.gamma_symmetric i).eq]

lemma gammaLinear_mulVec_sq (a : SpaceIndex → ℝ) (v : SpinIndex → ℝ) :
    ∑β, (M.gammaLinear a *ᵥ v) β ^ 2 = (∑i, a i ^ 2) * ∑β, v β ^ 2 := by
  simp only [pow_two]
  change (M.gammaLinear a *ᵥ v) ⬝ᵥ (M.gammaLinear a *ᵥ v) = _
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, (M.gammaLinear_symmetric a).eq,
    M.gammaLinear_sq]
  simp only [Matrix.vecMul_smul, Matrix.vecMul_one, smul_dotProduct, smul_eq_mul]
  simp only [pow_two, dotProduct]

def principalCoefficients (v : SpinIndex → ℝ) (ξ : Boson N) : FermionIndex N → ℝ :=
  fun p => (M.gammaLinear (fun i => ξ (i, p.2)) *ᵥ v) p.1

def principalSymbol (v : SpinIndex → ℝ) (ξ : Boson N) : Fermion N →L[ℂ] Fermion N :=
  M.cliffordLinear (M.principalCoefficients v ξ)

lemma principalCoefficients_sq (v : SpinIndex → ℝ) (ξ : Boson N) :
    ∑p, M.principalCoefficients v ξ p ^ 2 = (∑α, v α ^ 2) * ‖ξ‖ ^ 2 := by
  unfold principalCoefficients
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp_rw [M.gammaLinear_mulVec_sq]
  rw [← Finset.sum_mul, EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
    Finset.sum_comm]
  ring

lemma principalSymbol_sq (v : SpinIndex → ℝ) (ξ : Boson N) :
    M.principalSymbol v ξ * M.principalSymbol v ξ =
      (((1 / 2 : ℝ) * (∑α, v α ^ 2) * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
        (1 : Fermion N →L[ℂ] Fermion N) := by
  rw [principalSymbol, M.cliffordLinear_sq, M.principalCoefficients_sq]
  congr 1
  push_cast
  ring

lemma principalSymbol_norm_sq (v : SpinIndex → ℝ) (ξ : Boson N) (z : Fermion N) :
    ‖M.principalSymbol v ξ z‖ ^ 2 =
      ((1 / 2 : ℝ) * (∑α, v α ^ 2) * ‖ξ‖ ^ 2) * ‖z‖ ^ 2 := by
  rw [principalSymbol, M.cliffordLinear_norm_sq, M.principalCoefficients_sq]
  ring

lemma principalSymbol_unit_norm_sq (v : SpinIndex → ℝ) (hv : ∑α, v α ^ 2 = 1)
    (ξ : Boson N) (z : Fermion N) :
    ‖M.principalSymbol v ξ z‖ ^ 2 = (1 / 2 : ℝ) * ‖ξ‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [M.principalSymbol_norm_sq, hv, mul_one]

lemma coordinateDerivative_multiplier (i : SpaceIndex) (A : ColorIndex N)
    (g : Boson N → ℂ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (f : SmoothCore N) (x : Boson N) :
    coordinateDerivative i A (smoothMultiplier g hg f) x =
      g x • coordinateDerivative i A f x +
        (fderiv ℝ g x (EuclideanSpace.single (i, A) 1)) • f x := by
  rw [coordinateDerivative_apply, coordinateDerivative_apply]
  change fderiv ℝ (fun y => g y • f y) x _ = _
  rw [fderiv_fun_smul (hg.differentiable (by simp)).differentiableAt
    (f.contDiff.differentiable (by simp)).differentiableAt]
  rfl

lemma fermionAction_apply (α : SpinIndex) (A : ColorIndex N)
    (f : SmoothCore N) (x : Boson N) : M.fermionAction α A f x = M.theta α A (f x) := rfl

lemma smoothMultiplier_apply (g : Boson N → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (f : SmoothCore N) (x : Boson N) : smoothMultiplier g hg f x = g x • f x := rfl

lemma position_apply (i : SpaceIndex) (A : ColorIndex N)
    (f : SmoothCore N) (x : Boson N) : position i A f x = (x (i, A) : ℂ) • f x := rfl

lemma charge_apply (α : SpinIndex) (f : SmoothCore N) (x : Boson N) :
    M.charge α f x =
      (∑i : SpaceIndex, ∑A : ColorIndex N, ∑β : SpinIndex,
        (-Complex.I * (M.gamma i α β : ℂ)) •
          M.theta β A (coordinateDerivative i A f x)) +
      ∑i : SpaceIndex, ∑j : SpaceIndex, ∑A : ColorIndex N,
        ∑B : ColorIndex N, ∑C : ColorIndex N, ∑β : SpinIndex,
        ((((1 / 2 : ℝ) * M.structureConstant A B C * M.gammaTwo i j α β : ℝ) : ℂ) *
          (x (i, B) : ℂ) * (x (j, C) : ℂ)) • M.theta β A (f x) := by
  simp only [charge, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, IsAddApply.add_apply, sum_apply, IsSMulApply.smul_apply,
    fermionAction_apply, position_apply, map_smul, smul_smul, mul_assoc]

lemma charge_multiplier (α : SpinIndex) (g : Boson N → ℂ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (f : SmoothCore N) (x : Boson N) :
    M.charge α (smoothMultiplier g hg f) x =
      g x • M.charge α f x +
      ∑i : SpaceIndex, ∑A : ColorIndex N, ∑β : SpinIndex,
        (-Complex.I * (M.gamma i α β : ℂ) *
          fderiv ℝ g x (EuclideanSpace.single (i, A) 1)) • M.theta β A (f x) := by
  simp only [M.charge_apply, coordinateDerivative_multiplier, smoothMultiplier_apply,
    map_add, map_smul, smul_add, smul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  have hc (a b : ℂ) (z : Fermion N) : (a * (g x * b)) • z = (g x * (a * b)) • z := by
    congr 1
    ring
  have hd (a : ℂ) (z : Fermion N) : (a * g x) • z = (g x * a) • z := by
    rw [mul_comm a (g x)]
  simp_rw [hd]
  abel

def realCutoff (χ : Boson N → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    SmoothCore N →ₗ[ℂ] SmoothCore N :=
  smoothMultiplier (fun x => (χ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hχ)

def cutoffGradient (χ : Boson N → ℝ) (x : Boson N) : Boson N :=
  WithLp.toLp 2 (fun p => fderiv ℝ χ x (EuclideanSpace.single p 1))

lemma realCutoff_derivative (χ : Boson N → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (x : Boson N) (e : Boson N) :
    fderiv ℝ (fun y => (χ y : ℂ)) x e = (fderiv ℝ χ x e : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x
    (hχ.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact congrArg (fun L : Boson N →L[ℝ] ℂ => L e) h.fderiv

lemma principalCoefficients_basis (α : SpinIndex) (ξ : Boson N) (β : SpinIndex)
    (A : ColorIndex N) :
    M.principalCoefficients (Pi.single α 1) ξ (β, A) =
      ∑i, M.gamma i α β * ξ (i, A) := by
  simp only [principalCoefficients, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    Matrix.col_apply, gammaLinear, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← (M.gamma_symmetric i).apply α β]
  ring

lemma principalSymbol_basis_apply (α : SpinIndex) (ξ : Boson N) (z : Fermion N) :
    M.principalSymbol (Pi.single α 1) ξ z =
      ∑i : SpaceIndex, ∑A : ColorIndex N, ∑β : SpinIndex,
        ((M.gamma i α β * ξ (i, A) : ℝ) : ℂ) • M.theta β A z := by
  simp only [principalSymbol, cliffordLinear, sum_apply,
    IsSMulApply.smul_apply, Fintype.sum_prod_type, M.principalCoefficients_basis,
    Complex.ofReal_sum, Finset.sum_smul]
  conv_lhs =>
    arg 2
    ext β
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

lemma charge_realCutoff (α : SpinIndex) (χ : Boson N → ℝ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (f : SmoothCore N) (x : Boson N) :
    M.charge α (realCutoff χ hχ f) x =
      (χ x : ℂ) • M.charge α f x +
      (-Complex.I) • M.principalSymbol (Pi.single α 1) (cutoffGradient χ x) (f x) := by
  dsimp only [realCutoff]
  rw [M.charge_multiplier α (fun y => (χ y : ℂ))
    (Complex.ofRealCLM.contDiff.comp hχ) f x, M.principalSymbol_basis_apply]
  simp only [realCutoff_derivative χ hχ, Finset.smul_sum, smul_smul, Complex.ofReal_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro β hβ
  congr 1
  simp only [cutoffGradient]
  ring

def principalSymbolLinear (α : SpinIndex) :
    Boson N →ₗ[ℝ] (Fermion N →L[ℂ] Fermion N) where
  toFun ξ := M.principalSymbol (Pi.single α 1) ξ
  map_add' ξ η := by
    ext z : 1
    simp only [M.principalSymbol_basis_apply, IsAddApply.add_apply]
    simp only [PiLp.add_apply, mul_add, Complex.ofReal_add, add_smul,
      Finset.sum_add_distrib]
  map_smul' r ξ := by
    ext z : 1
    simp only [M.principalSymbol_basis_apply, IsSMulApply.smul_apply,
      Finset.smul_sum, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro A hA
    apply Finset.sum_congr rfl
    intro β hβ
    congr 1
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply]
    exact mul_left_comm (M.gamma i α β : ℂ) (r : ℂ) (ξ (i, A) : ℂ)

lemma basisSpinor_unit (α : SpinIndex) :
    (∑β : SpinIndex, ((Pi.single α 1 : SpinIndex → ℝ) β) ^ 2) = (1 : ℝ) := by
  classical
  simp only [Pi.single_apply, ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0)]
  simp

end AlgebraData
end
end BFSSQuantum

end OAI
