import OAI.Analysis.FreeEntropy.GaussianIBP

namespace OAI

noncomputable section
open scoped Polynomial
open MeasureTheory ProbabilityTheory Polynomial Finset
namespace FiniteEntropySeparation
 def realHermite (n : ℕ) : ℝ[X] := (Polynomial.hermite n).map (Int.castRingHom ℝ)
 @[simp] theorem realHermite_zero : realHermite 0 = 1 := by simp [realHermite]
 theorem realHermite_succ (n : ℕ) : realHermite (n+1) = X * realHermite n - (realHermite n).derivative := by
  simp [realHermite, Polynomial.hermite_succ, Polynomial.derivative_map]
 theorem realHermite_derivative (n : ℕ) : (realHermite (n+1)).derivative = (n+1 : ℝ) • realHermite n := by
  induction n with
  | zero => simp [realHermite_succ]
  | succ n ih =>
    rw [realHermite_succ (n+1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul, mul_smul_comm]
    calc
      _ = realHermite (n+1) + (n+1 : ℝ) • (X * realHermite n - (realHermite n).derivative) := by module
      _ = _ := by rw [← realHermite_succ]; push_cast; module
 theorem realHermite_monic (n : ℕ) : (realHermite n).Monic := (Polynomial.hermite_monic n).map _
 theorem realHermite_degree (n : ℕ) : (realHermite n).degree = n := by
  rw [realHermite, Polynomial.degree_map_eq_of_injective Int.cast_injective, Polynomial.degree_hermite]
 def hermiteSequence : Polynomial.Sequence ℝ := ⟨realHermite, realHermite_degree⟩
 def hermiteBasis : Module.Basis ℕ ℝ ℝ[X] := hermiteSequence.basis (fun n => by
  change IsUnit (realHermite n).leadingCoeff
  rw [(realHermite_monic n).leadingCoeff]; exact isUnit_one)
 @[simp] theorem hermiteBasis_apply (n : ℕ) : hermiteBasis n = realHermite n := by
  simp [hermiteBasis, hermiteSequence]
 def gaussianPolyIntegral (P : ℝ[X]) : ℝ := ∫ x, P.eval x ∂gaussianReal 0 1
 theorem gaussianPolyIntegral_add (P Q : ℝ[X]) :
    gaussianPolyIntegral (P+Q) = gaussianPolyIntegral P + gaussianPolyIntegral Q := by
  simp only [gaussianPolyIntegral, eval_add]
  exact integral_add (gaussian_polynomial_integrable _ _ _) (gaussian_polynomial_integrable _ _ _)
 theorem gaussianPolyIntegral_sub (P Q : ℝ[X]) :
    gaussianPolyIntegral (P-Q) = gaussianPolyIntegral P - gaussianPolyIntegral Q := by
  simp only [gaussianPolyIntegral, eval_sub]
  exact integral_sub (gaussian_polynomial_integrable _ _ _) (gaussian_polynomial_integrable _ _ _)
 theorem gaussianPolyIntegral_smul (r : ℝ) (P : ℝ[X]) :
    gaussianPolyIntegral (r • P) = r * gaussianPolyIntegral P := by
  simp [gaussianPolyIntegral, eval_smul, integral_const_mul]
 @[simp] theorem gaussianPolyIntegral_one : gaussianPolyIntegral 1 = 1 := by simp [gaussianPolyIntegral]
 @[simp] theorem gaussianPolyIntegral_zero : gaussianPolyIntegral 0 = 0 := by simp [gaussianPolyIntegral]
 theorem hermite_raising_lowering (n : ℕ) (Q : ℝ[X]) :
    gaussianPolyIntegral (realHermite (n+1) * Q) = gaussianPolyIntegral (realHermite n * Q.derivative) := by
  have hs := gaussian_polynomial_stein (realHermite n * Q)
  have hstein : gaussianPolyIntegral (X * (realHermite n * Q)) =
      gaussianPolyIntegral ((realHermite n * Q).derivative) := by
    simpa only [gaussianPolyIntegral, eval_mul, eval_X] using hs
  rw [realHermite_succ, sub_mul, gaussianPolyIntegral_sub, mul_assoc, hstein,
    derivative_mul, gaussianPolyIntegral_add]
  ring
 theorem realHermite_mean (n : ℕ) : gaussianPolyIntegral (realHermite n) = if n=0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using hermite_raising_lowering n 1
 theorem realHermite_inner (n m : ℕ) :
    gaussianPolyIntegral (realHermite n * realHermite m) = if n=m then (n.factorial : ℝ) else 0 := by
  induction n generalizing m with
  | zero => simpa [eq_comm] using realHermite_mean m
  | succ n ih =>
    cases m with
    | zero => simp [realHermite_mean]
    | succ m =>
      rw [hermite_raising_lowering, realHermite_derivative, mul_smul_comm, gaussianPolyIntegral_smul, ih]
      by_cases h : n=m
      · subst m; simp [Nat.factorial_succ]
      · simp [h]
 def gaussianPolyLinear : ℝ[X] →ₗ[ℝ] ℝ where
  toFun := gaussianPolyIntegral
  map_add' := gaussianPolyIntegral_add
  map_smul' := gaussianPolyIntegral_smul
 theorem hermite_expansion (P : ℝ[X]) : P = (hermiteBasis.repr P).sum (fun n a => a • realHermite n) := by
  simpa only [Finsupp.linearCombination_apply, hermiteBasis_apply] using (hermiteBasis.linearCombination_repr P).symm
 theorem hermite_sum_inner (a b : ℕ →₀ ℝ) :
    gaussianPolyIntegral (a.sum (fun n r => r • realHermite n) * b.sum (fun n r => r • realHermite n)) =
      a.sum (fun n r => r * b n * (n.factorial : ℝ)) := by
  classical
  change gaussianPolyLinear _ = _
  simp only [Finsupp.sum, sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, smul_eq_mul]
  rw [sum_comm]
  change (∑ n ∈ a.support, ∑ m ∈ b.support, b m*(a n*gaussianPolyIntegral (realHermite n*realHermite m))) = _
  simp_rw [realHermite_inner]
  apply sum_congr rfl
  intro n hn
  by_cases hnb : n ∈ b.support
  · rw [sum_eq_single n]
    · simp; ring
    · intro m hm hmn; simp [Ne.symm hmn]
    · exact fun h => (h hnb).elim
  · have hb : b n=0 := Finsupp.notMem_support_iff.mp hnb
    rw [hb, mul_zero, zero_mul]
    apply sum_eq_zero
    intro m hm
    have hnm : n ≠ m := fun h => hnb (h.symm ▸ hm)
    simp [hnm]
end FiniteEntropySeparation

end

end OAI
