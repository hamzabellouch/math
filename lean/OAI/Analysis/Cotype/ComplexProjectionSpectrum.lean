import OAI.Analysis.Cotype.ComplexProjectionPolynomial

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem complexProjectionProduct_weighted_sum {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℂ) (P : Fin n → Ω → Z →L[ℂ] Z) :
    complexProjectionProduct (fun i => ∑ a, w i a • P i a) =
      ∑ ω : Fin n → Ω, (∏ i, w i (ω i)) • complexProjectionProduct (fun i => P i (ω i)) := by
  classical
  induction n with
  | zero => simp [complexProjectionProduct]
  | succ n ih =>
    rw [← (projectionChoiceCons Ω n).sum_comp]
    simp only [Fintype.sum_prod_type, projectionChoiceCons, Equiv.coe_fn_mk,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, complexProjectionProduct]
    rw [ih]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_comm]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def complexSpectralEval {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (f : Cube m → ℂ) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  ∑ ε, f ε • complexDualLift (projectionPattern P ε)

@[simp] theorem complexDualLift_zero : complexDualLift (0 : Y →L[ℝ] Y) = 0 :=
  map_zero (complexDualLiftCLM (Y := Y))

theorem complexSpectralEval_one {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    complexSpectralEval P 1 = 1 := by
  simp only [complexSpectralEval, Pi.one_apply, one_smul]
  change (∑ ε, complexDualLiftCLM (projectionPattern P ε)) = 1
  rw [← map_sum]
  simp only [complexDualLiftCLM_apply, projectionPattern_sum, complexDualLift_one]

theorem complexSpectralEval_mul {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (f g : Cube m → ℂ) :
    complexSpectralEval P f * complexSpectralEval P g = complexSpectralEval P (f*g) := by
  classical
  have hpat (ε η : Cube m) :
      complexDualLift (projectionPattern P ε) * complexDualLift (projectionPattern P η) =
        if ε = η then complexDualLift (projectionPattern P ε) else 0 := by
    rw [← complexDualLift_mul, projectionPattern_mul P hp hc]
    split_ifs <;> simp
  have hmul_smul (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)
      (scalar : ℂ) : left * (scalar • right) = scalar • (left * right) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact left.map_smul scalar (right vector)
  have hsmul_mul (scalar : ℂ) (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :
      (scalar • left) * right = scalar • (left * right) := by
    apply ContinuousLinearMap.ext
    intro vector
    rfl
  have hsmul_zero (scalar : ℂ) :
      scalar • (0 : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = 0 := by
    ext vector dual
    exact mul_zero scalar
  simp only [complexSpectralEval, Finset.sum_mul, Finset.mul_sum,
    hsmul_mul, hmul_smul, Finset.smul_sum, hpat]
  simp [smul_ite, Pi.mul_apply, smul_smul, mul_comm, hsmul_zero]

def projectionDegree {m : ℕ} (ε : Cube m) : ℕ :=
  (Finset.univ.filter (fun i => ε i = true)).card

theorem projectionDegree_le {m : ℕ} (ε : Cube m) : projectionDegree ε ≤ m := by
  simpa [projectionDegree] using
    Finset.card_le_card (Finset.filter_subset (fun i => ε i = true) (Finset.univ : Finset (Fin m)))

theorem projectionPattern_weight {m : ℕ} (ε : Cube m) (z : ℂ) :
    (∏ i, if ε i then z else 1) = z^(projectionDegree ε) := by
  classical
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, projectionDegree]

theorem complexProjectionPolynomial_spectral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (z : ℂ) :
    complexProjectionPolynomial P z = complexSpectralEval P (fun ε => z^(projectionDegree ε)) := by
  have h := complexProjectionProduct_weighted_sum
    (fun (_ : Fin m) (b : Bool) => if b then z else 1)
    (fun i (b : Bool) => complexDualLift (if b then 1-P i else P i))
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, one_smul,
    complexDualLift_sub, complexDualLift_one] at h
  unfold complexProjectionPolynomial complexSpectralEval
  calc
    _ = ∑ ε : Cube m, (∏ i, if ε i then z else 1) •
        complexProjectionProduct (fun i => complexDualLift (if ε i then 1-P i else P i)) := by
      simpa only [add_comm] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ε _
      rw [projectionPattern_weight, complexProjectionProduct_lift]
      rfl

end Cotype

end

end OAI
