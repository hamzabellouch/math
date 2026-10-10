import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockCoefficientBounds

namespace OAI

/-! A rationally evaluable budget suffices for every physical simulator coefficient. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {κ : Type*} [Fintype κ]

def qmaXZInputSize (J : κ → ℝ) : ℝ := Fintype.card κ+∑ e, |J e|

def qmaXZPolynomialBudget (J : κ → ℝ) : ℝ :=
  1+2000000*qmaXZInputSize J+(7056*qmaXZInputSize J)^2

theorem qmaXZBlockBudget_bound (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    qmaXZBlockBudget t J ≤ qmaXZPolynomialBudget J := by
  let U := qmaXZInputSize J
  have hU : 0 ≤ U := by dsimp [U,qmaXZInputSize]; positivity
  have hs : (∑ e, |J e|) ≤ U := by
    dsimp [U,qmaXZInputSize]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hp : (∑ e : QMAXZPairIndex t, (1+|J e.val|)) ≤ U := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    have hc := Fintype.card_subtype_le (fun e => (t e).IsPair)
    change Fintype.card (QMAXZPairIndex t) ≤ Fintype.card κ at hc
    exact add_le_add (by exact_mod_cast hc) (qmaSum_subtype_abs_le (fun e => (t e).IsPair) J)
  have hf := (qmaSum_subtype_abs_le (fun e => (t e).IsField) J).trans hs
  have hc := (qmaXZFamilyConstant_bound t J).trans
    (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hpair0 : 0 ≤ ∑ e : QMAXZPairIndex t, (1+|J e.val|) := by positivity
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ) ≤ 7056) hpair0)
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 7056)) 2
  change 1+7056*(∑ e : QMAXZPairIndex t, (1+|J e.val|))+
      (1228800*(∑ e : QMAXZPairIndex t, (1+|J e.val|))+
        7*(∑ e : QMAXZFieldIndex t, |J e.val|)+|qmaXZFamilyConstant t J|)+
      (7056*(∑ e : QMAXZPairIndex t, (1+|J e.val|)))^2 ≤
    1+2000000*U+(7056*U)^2
  nlinarith

variable {τ : Type*} [Fintype τ]

theorem qmaFourTensorFull_accuracy_of_budget (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f})
    (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant B : ℝ)
    (hbudget : qmaFourTensorFullBudget t weight constant ≤ B) (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaFourTensorPhysicalMatrix (9*B^3*N)
        (((9*B^3*N:ℝ):ℂ) • qmaFourTensorFamilyCoupling left right a b t+
          qmaFourTensorFullCounterterm left right a b t site axis weight constant))-
      MediatorGraph.normalizedBottom (qmaFourTensorFullTarget left right a b t site axis weight constant)| ≤ 1/(N:ℝ) := by
  let V := qmaFourTensorFamilyCoupling left right a b t
  let C := qmaFourTensorFullCounterterm left right a b t site axis weight constant
  have hB := (qmaFourTensorFull_budget left right a b t site axis weight constant).trans hbudget
  have hb := qmaFourTensorNormBudget_bounds V C
  have hCs : C.conjTranspose = C := by
    simp only [C,qmaFourTensorFullCounterterm,Matrix.conjTranspose_add,qmaFourTensorFamilyCounterterm_star,
      qmaFourTensorOnsite_star]
  have h := qmaFourTensor_polynomial_accuracy B (hb.1.trans hB)
    V C (qmaFourTensorFamily_star left right a b t hneq) hCs
    (qmaFourTensorFamily_orthogonal left right a b t hneq)
    (qmaFourTensorFamily_excitation left right a b t hneq)
    (hb.2.1.trans hB) (hb.2.2.1.trans hB) (hb.2.2.2.trans hB)
    (EuclideanSpace.single (fun _ => 0) 1) (by simp [PiLp.norm_single]) N hN
  rw [show qmaFourTensorEffectiveMatrix V C = qmaFourTensorFullTarget left right a b t site axis weight constant
    from qmaFourTensorFull_effective left right a b t hneq hdist site axis weight constant] at h
  exact h

omit [Fintype τ] in
theorem qmaXZBlock_polynomial_accuracy (t : κ → QMAXZTerm n) (J : κ → ℝ)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaXZBlockSource (9*(qmaXZPolynomialBudget J)^3*N) t J)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 1/(N:ℝ) := by
  have h := qmaFourTensorFull_accuracy_of_budget
    (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
    (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
    (fun e => J e.val)
    (fun e => (qmaXZPairData t e).distinct)
    (fun e f hef => qmaXZPairData_distinct t hprivate e f hef)
    (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
    (fun e => J e.val) (qmaXZFamilyConstant t J) (qmaXZPolynomialBudget J)
    (qmaXZBlockBudget_bound t J) N hN
  rw [qmaXZFamily_target,
    ← qmaBlockSourceFull_reindex _ _ _ _ _ _ (fun e => (qmaXZPairData t e).distinct),
    MediatorGraph.normalizedBottom_reindex] at h
  exact h

end ContinuumCoulomb

end

end OAI
