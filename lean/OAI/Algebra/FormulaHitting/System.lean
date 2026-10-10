import OAI.Algebra.FormulaHitting.Representation
import OAI.Algebra.FormulaHitting.Series
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PowerSeries.Inverse

namespace OAI

noncomputable section
namespace NCHitting
namespace AcyclicRepresentation

open Matrix
variable {F : Type*} {n : ℕ} [Field F] [CharZero F]

omit [CharZero F] in
theorem J_sum {I : Type*} (i : ℕ) (s : Finset I) (f : I → PowerSeries F) :
    J i (∑ a ∈ s, f a) = ∑ a ∈ s, J i (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, J_add, ih]

omit [CharZero F] in
theorem J_C_mul (i : ℕ) (c : F) (f : PowerSeries F) :
    J i (PowerSeries.C c * f) = PowerSeries.C c * J i f := by
  simpa only [PowerSeries.smul_eq_C_mul] using J_smul i c f

def systemLevel (R : AcyclicRepresentation F n) :
    ℕ → Matrix R.State R.State (PowerSeries F)
  | 0 => 1
  | k + 1 => fun a b => ∑ i : Fin n, ∑ c : R.State,
      PowerSeries.C (R.B i a c) * J (i.val + 1) (systemLevel R k c b)

def systemMatrix (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (PowerSeries F) :=
  fun a b => ∑ i : Fin n, PowerSeries.C (R.B i a b) * kernel (i.val + 1)

def fundamentalMatrix (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (PowerSeries F) :=
  fun a b => ∑ k ∈ Finset.range (Fintype.card R.State), R.systemLevel k a b

def denominator (n : ℕ) : Polynomial F :=
  ∏ i : Fin n, (Polynomial.X + Polynomial.C ((i.val + 1 : ℕ) : F))

def cofactor (i : Fin n) : Polynomial F :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X + Polynomial.C ((j.val + 1 : ℕ) : F))

def systemNumerator (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (Polynomial F) :=
  fun a b => ∑ i : Fin n, Polynomial.C (R.B i a b) * cofactor i

omit [CharZero F] in
theorem denominator_eq (i : Fin n) : denominator (F := F) n =
    (Polynomial.X + Polynomial.C ((i.val + 1 : ℕ) : F)) * cofactor i := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

omit [CharZero F] in
theorem denominator_degree : (denominator (F := F) n).natDegree ≤ n := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  simp only [Polynomial.natDegree_X_add_C]
  simp

omit [CharZero F] in
theorem cofactor_degree (i : Fin n) : (cofactor (F := F) i).natDegree ≤ n - 1 := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  simp only [Polynomial.natDegree_X_add_C]
  simp

omit [CharZero F] in
theorem systemNumerator_degree (R : AcyclicRepresentation F n) (a b : R.State) :
    (R.systemNumerator a b).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (cofactor_degree i)

theorem denominator_eval_zero_ne : (denominator (F := F) n).eval 0 ≠ 0 := by
  simp only [denominator, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, zero_add]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val)

theorem denominator_mul_kernel (i : Fin n) :
    (denominator (F := F) n : PowerSeries F) * kernel (i.val + 1) =
      (cofactor (F := F) i : PowerSeries F) := by
  rw [denominator_eq i]
  simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
  calc
    (PowerSeries.X + PowerSeries.C ((i.val + 1 : ℕ) : F)) *
        (cofactor (F := F) i : PowerSeries F) * kernel (i.val + 1) =
        (cofactor (F := F) i : PowerSeries F) *
          (kernel (i.val + 1) * (PowerSeries.X + PowerSeries.C ((i.val + 1 : ℕ) : F))) := by ring
    _ = _ := by rw [kernel_mul_linear _ (Nat.succ_ne_zero _)]; simp

omit [CharZero F] in
theorem polynomial_coe_sum {I : Type*} [Fintype I] (p : I → Polynomial F) :
    ((∑ i, p i : Polynomial F) : PowerSeries F) = ∑ i, (p i : PowerSeries F) :=
  map_sum Polynomial.coeToPowerSeries.ringHom p Finset.univ

theorem denominator_mul_systemMatrix (R : AcyclicRepresentation F n) (a b : R.State) :
    (denominator (F := F) n : PowerSeries F) * R.systemMatrix a b =
      (R.systemNumerator a b : PowerSeries F) := by
  simp only [systemMatrix, systemNumerator, polynomial_coe_sum, Polynomial.coe_mul,
    Polynomial.coe_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, denominator_mul_kernel]

omit [CharZero F] in
theorem systemLevel_wordSum (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) :
    R.systemLevel k a b = ∑ w ∈ wordsOfLength n k,
      PowerSeries.C (wordMatrix R.B w a b) * wordSeries w := by
  induction k generalizing a b with
  | zero =>
    by_cases h : a = b <;>
      simp [systemLevel, wordsOfLength, wordMatrix, Matrix.one_apply, h]
  | succ k ih =>
    rw [sum_wordsOfLength_succ]
    simp only [systemLevel, ih, J_sum, J_C_mul, wordSeries_cons,
      wordMatrix, List.map_cons, List.prod_cons, Matrix.mul_apply,
      map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm

def contract (R : AcyclicRepresentation F n) :
    Matrix R.State R.State (PowerSeries F) →ₗ[PowerSeries F] PowerSeries F where
  toFun M := (fun a => PowerSeries.C (R.u a)) ⬝ᵥ
    (M *ᵥ (fun b => PowerSeries.C (R.v b)))
  map_add' M N := by simp [add_mulVec, dotProduct_add]
  map_smul' c M := by simp [smul_mulVec, dotProduct_smul]

omit [CharZero F] in
theorem contract_eq_sum (R : AcyclicRepresentation F n)
    (M : Matrix R.State R.State (PowerSeries F)) :
    R.contract M = ∑ b : R.State, PowerSeries.C (R.v b) *
      ∑ a : R.State, PowerSeries.C (R.u a) * M a b := by
  simp only [contract, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [CharZero F] in
theorem contract_wordMatrix (R : AcyclicRepresentation F n) (w : Word n) :
    R.contract ((wordMatrix R.B w).map PowerSeries.C) = PowerSeries.C (R.value w) := by
  rw [R.value_eq_matrix]
  simp [contract, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

omit [CharZero F] in
theorem systemLevel_eq_sum (R : AcyclicRepresentation F n) (k : ℕ) :
    R.systemLevel k = ∑ w ∈ wordsOfLength n k,
      wordSeries (F := F) w • (wordMatrix R.B w).map PowerSeries.C := by
  apply Matrix.ext
  intro a b
  simpa [Matrix.sum_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
    R.systemLevel_wordSum k a b

omit [CharZero F] in
theorem fundamentalMatrix_eq_sum (R : AcyclicRepresentation F n) :
    R.fundamentalMatrix =
      ∑ k ∈ Finset.range (Fintype.card R.State), R.systemLevel k := by
  apply Matrix.ext
  intro a b
  simp [fundamentalMatrix, Matrix.sum_apply]

omit [CharZero F] in
theorem contract_fundamentalMatrix (R : AcyclicRepresentation F n) :
    R.contract R.fundamentalMatrix =
      ∑ k ∈ Finset.range (Fintype.card R.State), ∑ w ∈ wordsOfLength n k,
        PowerSeries.C (R.value w) * wordSeries w := by
  rw [fundamentalMatrix_eq_sum]
  simp [systemLevel_eq_sum, contract_wordMatrix, smul_eq_mul, mul_comm]

omit [CharZero F] in
theorem systemLevel_constant_zero (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) :
    PowerSeries.constantCoeff (R.systemLevel (k + 1) a b) = 0 := by
  simp [systemLevel]

omit [CharZero F] in
theorem systemLevel_entry_zero (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) (h : R.rank b < R.rank a + k) :
    R.systemLevel k a b = 0 := by
  induction k generalizing a with
  | zero =>
    have hne : a ≠ b := by intro he; subst b; simp at h
    simp [systemLevel, hne]
  | succ k ih =>
    simp only [systemLevel]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : R.rank c ≤ R.rank a
    · simp [R.upper i a c hc]
    · have hbc : R.rank b < R.rank c + k := by omega
      rw [ih c hbc]
      simp

omit [CharZero F] in
theorem systemLevel_eq_zero (R : AcyclicRepresentation F n)
    (k : ℕ) (h : Fintype.card R.State ≤ k) : R.systemLevel k = 0 := by
  apply Matrix.ext
  intro a b
  apply R.systemLevel_entry_zero k a b
  have hb := R.rank_lt b
  omega

theorem derivative_systemLevel (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) :
    PowerSeries.derivative (R := F) (R.systemLevel (k + 1) a b) =
      (R.systemMatrix * R.systemLevel k) a b := by
  simp only [systemLevel, map_sum, Derivation.leibniz, smul_eq_mul, derivative_J,
    PowerSeries.derivative_C, systemMatrix, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [CharZero F] in
theorem fundamentalMatrix_constant (R : AcyclicRepresentation F n)
    (hm : 0 < Fintype.card R.State) :
    R.fundamentalMatrix.map PowerSeries.constantCoeff = 1 := by
  apply Matrix.ext
  intro a b
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Matrix.map_apply, fundamentalMatrix, hk,
    Finset.sum_range_succ']
  simp [systemLevel, Matrix.one_apply]

omit [CharZero F] in
theorem fundamentalMatrix_isUnit (R : AcyclicRepresentation F n)
    (hm : 0 < Fintype.card R.State) : IsUnit R.fundamentalMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply (PowerSeries.isUnit_iff_constantCoeff).mpr
  have hc : PowerSeries.constantCoeff R.fundamentalMatrix.det = 1 := by
    rw [RingHom.map_det]
    change (R.fundamentalMatrix.map PowerSeries.constantCoeff).det = 1
    rw [R.fundamentalMatrix_constant hm, Matrix.det_one]
  rw [hc]
  exact isUnit_one

theorem fundamentalMatrix_derivative (R : AcyclicRepresentation F n) :
    R.fundamentalMatrix.map (PowerSeries.derivative (R := F)) =
      R.systemMatrix * R.fundamentalMatrix := by
  apply Matrix.ext
  intro a b
  let D : ℕ → PowerSeries F := fun k => PowerSeries.derivative (R := F) (R.systemLevel k a b)
  have hD0 : D 0 = 0 := by
    by_cases h : a = b <;> simp [D, systemLevel, h]
  have hDm : D (Fintype.card R.State) = 0 := by
    simp [D, R.systemLevel_eq_zero _ (le_refl _)]
  have hshift : (∑ k ∈ Finset.range (Fintype.card R.State), D k) =
      ∑ k ∈ Finset.range (Fintype.card R.State), D (k + 1) := by
    have hleft := Finset.sum_range_succ D (Fintype.card R.State)
    have hright := Finset.sum_range_succ' D (Fintype.card R.State)
    simpa [hD0, hDm] using hleft.symm.trans hright
  simp only [Matrix.map_apply, fundamentalMatrix, map_sum]
  change (∑ k ∈ Finset.range (Fintype.card R.State), D k) = _
  rw [hshift]
  simp only [D, derivative_systemLevel, Matrix.mul_apply, fundamentalMatrix,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem fundamentalMatrix_polynomial_system (R : AcyclicRepresentation F n)
    (a b : R.State) :
    (denominator (F := F) n : PowerSeries F) *
        PowerSeries.derivative (R := F) (R.fundamentalMatrix a b) =
      ∑ c : R.State, (R.systemNumerator a c : PowerSeries F) *
        R.fundamentalMatrix c b := by
  have hder := congrFun (congrFun R.fundamentalMatrix_derivative a) b
  change PowerSeries.derivative (R := F) (R.fundamentalMatrix a b) =
    ∑ c : R.State, R.systemMatrix a c * R.fundamentalMatrix c b at hder
  rw [hder, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_assoc, denominator_mul_systemMatrix]

end AcyclicRepresentation

theorem Formula.system_output {F : Type*} {n : ℕ} [Field F] [CharZero F]
    (f : Formula F n) :
    f.representation.contract f.representation.fundamentalMatrix =
      ∑ k ∈ Finset.range (Fintype.card f.representation.State),
        ∑ w ∈ wordsOfLength n k, PowerSeries.C (f.coeff w) * wordSeries w := by
  simp only [AcyclicRepresentation.contract_fundamentalMatrix, Formula.representation_correct]

end NCHitting

end

end OAI
