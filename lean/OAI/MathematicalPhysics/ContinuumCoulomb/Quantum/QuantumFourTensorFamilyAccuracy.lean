import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorOperatorBounds

namespace OAI

/-! A polynomial-precision simulator for an arbitrary family of distinct X/Z pairs. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaFourTensorFamilyTarget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :=
  (∑ e, (t e:ℂ) • qmaPairMatrix (left e) (right e) (qmaFourAxis (a e)) (qmaFourAxis (b e)))+
    ((∑ e, qmaFourEnergyOffset (a e) (b e) (t e):ℝ):ℂ) •
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)

def qmaFourTensorFamilyBudget (t : κ → ℝ) : ℝ :=
  let s := ∑ e, (1+|t e|)
  1+7056*s+1228800*s+(7056*s)^2

theorem qmaFourTensorFamily_effective_eq (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f}) :
    qmaFourTensorEffectiveMatrix (qmaFourTensorFamilyCoupling left right a b t)
      (qmaFourTensorFamilyCounterterm left right a b t) = qmaFourTensorFamilyTarget left right a b t := by
  have h := qmaFourTensorFamily_effective left right a b t hneq hdist
  change _ = qmaFourTensorFamilyTarget left right a b t at h
  rw [qmaFourTensorEffectiveMatrix]
  rw [← h]
  module

theorem qmaFourTensorFamily_budget_bounds (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    1 ≤ qmaFourTensorFamilyBudget t ∧
      ‖spinMatrixOperator (qmaFourTensorFamilyCoupling left right a b t)‖ ≤ qmaFourTensorFamilyBudget t ∧
      ‖spinMatrixOperator (qmaFourTensorFamilyCounterterm left right a b t)‖ ≤ qmaFourTensorFamilyBudget t ∧
      ‖spinMatrixOperator (qmaFourTensorEffectiveMatrix (qmaFourTensorFamilyCoupling left right a b t)
        (qmaFourTensorFamilyCounterterm left right a b t))‖ ≤ qmaFourTensorFamilyBudget t := by
  let V := qmaFourTensorFamilyCoupling left right a b t
  let C := qmaFourTensorFamilyCounterterm left right a b t
  let s := ∑ e, (1+|t e|)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun _ _ => by positivity)
  have hv : ‖spinMatrixOperator V‖ ≤ 7056*s := qmaFourTensorFamily_norm left right a b t
  have hcoeff : (∑ e, |t e|) ≤ s := Finset.sum_le_sum (fun _ _ => by linarith)
  have hc : ‖spinMatrixOperator C‖ ≤ 1228800*s :=
    (qmaFourTensorFamilyCounterterm_bound left right a b t).trans
      (mul_le_mul_of_nonneg_left hcoeff (by norm_num))
  have hb : qmaFourTensorNormBudget V C ≤ qmaFourTensorFamilyBudget t := by
    have hv2 := pow_le_pow_left₀ (norm_nonneg (spinMatrixOperator V)) hv 2
    change 1+‖spinMatrixOperator V‖+‖spinMatrixOperator C‖+‖spinMatrixOperator V‖^2 ≤
      1+7056*s+1228800*s+(7056*s)^2
    linarith
  have h := qmaFourTensorNormBudget_bounds V C
  exact ⟨h.1.trans hb,h.2.1.trans hb,h.2.2.1.trans hb,h.2.2.2.trans hb⟩

theorem qmaFourTensorFamily_accuracy (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (u : EuclideanSpace ℂ (Fin n → Fin 2)) (hu : ‖u‖ = 1) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix (9*(qmaFourTensorFamilyBudget t)^3*N)
        (((9*(qmaFourTensorFamilyBudget t)^3*N:ℝ):ℂ) • qmaFourTensorFamilyCoupling left right a b t+
          qmaFourTensorFamilyCounterterm left right a b t))-
      MediatorGraph.normalizedBottom (qmaFourTensorFamilyTarget left right a b t)| ≤ 1/(N:ℝ) := by
  have hb := qmaFourTensorFamily_budget_bounds left right a b t
  have h := qmaFourTensor_polynomial_accuracy (qmaFourTensorFamilyBudget t) hb.1
    (qmaFourTensorFamilyCoupling left right a b t) (qmaFourTensorFamilyCounterterm left right a b t)
    (qmaFourTensorFamily_star left right a b t hneq)
    (qmaFourTensorFamilyCounterterm_star left right a b t)
    (qmaFourTensorFamily_orthogonal left right a b t hneq)
    (qmaFourTensorFamily_excitation left right a b t hneq) hb.2.1 hb.2.2.1 hb.2.2.2 u hu N hN
  rwa [qmaFourTensorFamily_effective_eq left right a b t hneq hdist] at h

end ContinuumCoulomb

end

end OAI
