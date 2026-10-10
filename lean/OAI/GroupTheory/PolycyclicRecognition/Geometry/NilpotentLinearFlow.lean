import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateOperations
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! # Polynomial linear flows used in the logarithm of a lattice automorphism -/

noncomputable section
namespace PolycyclicRecognition

section Algebra
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
local instance linearFlowRationalModule : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)

def nilpotentLinearFlow (D : Module.End ℝ V) (t : ℝ) : Module.End ℝ V :=
  IsNilpotent.exp (t • D)

theorem nilpotentLinearFlow_add (D : Module.End ℝ V) (hD : IsNilpotent D) (s t : ℝ) :
    nilpotentLinearFlow D (s + t) = nilpotentLinearFlow D s * nilpotentLinearFlow D t := by
  have hc : Commute (s • D) (t • D) := by
    change (s • D) * (t • D) = (t • D) * (s • D)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm s t]
  change IsNilpotent.exp ((s + t) • D) = IsNilpotent.exp (s • D) * IsNilpotent.exp (t • D)
  rw [add_smul]
  exact IsNilpotent.exp_add_of_commute hc (hD.smul s) (hD.smul t)

theorem nilpotentLinearFlow_nat (D : Module.End ℝ V) (hD : IsNilpotent D) (n : ℕ) :
    nilpotentLinearFlow D (n : ℝ) = IsNilpotent.exp D ^ n := by
  induction n with
  | zero => simp [nilpotentLinearFlow]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, nilpotentLinearFlow_add D hD, ih, pow_succ]
    simp only [nilpotentLinearFlow, one_smul]

theorem nilpotentLinearFlow_eq_sum (D : Module.End ℝ V) {k : ℕ} (hk : D ^ k = 0)
    (t : ℝ) (x : V) :
    nilpotentLinearFlow D t x =
      ∑ i ∈ Finset.range k, t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x) := by
  have ht : (t • D) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  rw [nilpotentLinearFlow, IsNilpotent.exp_eq_sum ht]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

theorem coordinatePolynomial_nilpotentLinearFlow {d : ℕ}
    (b : Module.Basis (Fin d) ℝ V) (D : Module.End ℝ V) (hD : IsNilpotent D) (x : V) :
    IsCoordinatePolynomial (fun t : Fin 1 → ℝ => b.equivFun (nilpotentLinearFlow D (t 0) x)) := by
  obtain ⟨k, hk⟩ := hD
  refine ⟨fun j => ∑ i ∈ Finset.range k,
    MvPolynomial.X 0 ^ i * MvPolynomial.C (b.equivFun (((i.factorial : ℚ)⁻¹ • D ^ i) x) j), ?_⟩
  intro t j
  change MvPolynomial.eval t _ = b.equivFun (nilpotentLinearFlow D (t 0) x) j
  rw [nilpotentLinearFlow_eq_sum D hk]
  simp only [map_sum, map_smul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_mul,
    map_pow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end Algebra

section Derivative
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
local instance linearFlowDerivativeRationalModule : Module ℚ V := Module.compHom V (algebraMap ℚ ℝ)

theorem hasDerivAt_nilpotentLinearFlow_zero (D : Module.End ℝ V) (hD : IsNilpotent D)
    (x : V) : HasDerivAt (fun t : ℝ => nilpotentLinearFlow D t x) (D x) 0 := by
  obtain ⟨k, hk⟩ := hD
  have hk' : D ^ (k + 2) = 0 := by rw [pow_add, hk, zero_mul]
  have hterm (i : ℕ) :
      HasDerivAt (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x))
        (if i = 1 then D x else 0) 0 := by
    have hh : HasDerivAt
        (fun t : ℝ => t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x))
        (((i : ℝ) * 0 ^ (i - 1)) • (((i.factorial : ℚ)⁻¹ • D ^ i) x)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow i).smul_const
        (((i.factorial : ℚ)⁻¹ • D ^ i) x)
    convert hh using 1
    by_cases hi : i = 1
    · subst i
      simp
    · by_cases hz : i = 0
      · subst i
        simp
      · have hsub : i - 1 ≠ 0 := by omega
        simp [hi, zero_pow hsub]
  have hsum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.range (k + 2)) => hterm i)
  have heq : (fun t : ℝ => nilpotentLinearFlow D t x) =
      (fun t => ∑ i ∈ Finset.range (k + 2),
        t ^ i • (((i.factorial : ℚ)⁻¹ • D ^ i) x)) :=
    funext (fun t => nilpotentLinearFlow_eq_sum D hk' t x)
  rw [heq]
  simpa using hsum

end Derivative
end PolycyclicRecognition

end

end OAI
