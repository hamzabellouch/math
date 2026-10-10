import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorOnsite

namespace OAI

/-! Full X/Z families, including scalar and one-site terms, have polynomial simulators. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ τ : Type*} [Fintype κ] [Fintype τ]

def qmaFourTensorFullCounterterm (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :=
  qmaFourTensorFamilyCounterterm left right a b t+qmaFourTensorOnsite site axis weight constant

def qmaFourTensorFullTarget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :=
  qmaFourTensorFamilyTarget left right a b t+
    ((∑ e, (weight e:ℂ) • qmaSiteMatrix (site e) (qmaFourAxis (axis e)))+(constant:ℂ) • 1)

def qmaFourTensorFullBudget (t : κ → ℝ) (weight : τ → ℝ) (constant : ℝ) : ℝ :=
  let s := ∑ e, (1+|t e|)
  let c := 1228800*s+7*(∑ e, |weight e|)+|constant|
  1+7056*s+c+(7056*s)^2

theorem qmaFourTensorFull_effective (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    qmaFourTensorEffectiveMatrix (qmaFourTensorFamilyCoupling left right a b t)
      (qmaFourTensorFullCounterterm left right a b t site axis weight constant) =
        qmaFourTensorFullTarget left right a b t site axis weight constant := by
  rw [qmaFourTensorFullTarget,← qmaFourTensorFamily_effective_eq left right a b t hneq hdist]
  simp only [qmaFourTensorEffectiveMatrix,qmaFourTensorFullCounterterm,Matrix.mul_add,Matrix.add_mul]
  rw [qmaFourTensorOnsite_compression]
  abel

theorem qmaFourTensorFull_budget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    qmaFourTensorNormBudget (qmaFourTensorFamilyCoupling left right a b t)
      (qmaFourTensorFullCounterterm left right a b t site axis weight constant) ≤
        qmaFourTensorFullBudget t weight constant := by
  let s := ∑ e, (1+|t e|)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun _ _ => by positivity)
  have hcoeff : (∑ e, |t e|) ≤ s := Finset.sum_le_sum (fun _ _ => by linarith)
  have hv := qmaFourTensorFamily_norm left right a b t
  have hc : ‖spinMatrixOperator (qmaFourTensorFullCounterterm left right a b t site axis weight constant)‖ ≤
      1228800*s+7*(∑ e, |weight e|)+|constant| := by
    rw [qmaFourTensorFullCounterterm,spinMatrixOperator_add]
    apply (norm_add_le _ _).trans
    have hp := (qmaFourTensorFamilyCounterterm_bound left right a b t).trans
      (mul_le_mul_of_nonneg_left hcoeff (by norm_num))
    have hf := qmaFourTensorOnsite_norm site axis weight constant
    linarith
  have hv2 := pow_le_pow_left₀ (norm_nonneg (spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t))) hv 2
  change 1+‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖+
    ‖spinMatrixOperator (qmaFourTensorFullCounterterm left right a b t site axis weight constant)‖+
    ‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖^2 ≤
      1+7056*s+(1228800*s+7*(∑ e, |weight e|)+|constant|)+(7056*s)^2
  linarith

theorem qmaFourTensorFull_accuracy (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix
        (9*(qmaFourTensorFullBudget t weight constant)^3*N)
        (((9*(qmaFourTensorFullBudget t weight constant)^3*N:ℝ):ℂ) •
          qmaFourTensorFamilyCoupling left right a b t+
          qmaFourTensorFullCounterterm left right a b t site axis weight constant))-
      MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b t site axis weight constant)| ≤ 1/(N:ℝ) := by
  let V := qmaFourTensorFamilyCoupling left right a b t
  let C := qmaFourTensorFullCounterterm left right a b t site axis weight constant
  have hB := qmaFourTensorFull_budget left right a b t site axis weight constant
  have hb := qmaFourTensorNormBudget_bounds V C
  have hCs : C.conjTranspose = C := by
    simp only [C,qmaFourTensorFullCounterterm,Matrix.conjTranspose_add,qmaFourTensorFamilyCounterterm_star,
      qmaFourTensorOnsite_star]
  have h := qmaFourTensor_polynomial_accuracy (qmaFourTensorFullBudget t weight constant) (hb.1.trans hB)
    V C (qmaFourTensorFamily_star left right a b t hneq) hCs
    (qmaFourTensorFamily_orthogonal left right a b t hneq)
    (qmaFourTensorFamily_excitation left right a b t hneq)
    (hb.2.1.trans hB) (hb.2.2.1.trans hB) (hb.2.2.2.trans hB)
    (EuclideanSpace.single (fun _ => 0) 1) (by simp [PiLp.norm_single]) N hN
  rw [show qmaFourTensorEffectiveMatrix V C = qmaFourTensorFullTarget left right a b t site axis weight constant
    from qmaFourTensorFull_effective left right a b t hneq hdist site axis weight constant] at h
  exact h

end ContinuumCoulomb

end

end OAI
