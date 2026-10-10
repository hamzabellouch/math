import Mathlib.Algebra.Polynomial.Degree.Monomial
import Mathlib.Algebra.Polynomial.Derivative
import OAI.AlgebraicGeometry.PlaneCurves.MovingConfigurations

namespace OAI

/-!
# Projective line intersections, singular intersections, and binary roots
-/

section

noncomputable section
namespace Nagata.Workers.W14

 theorem polynomial_zero_of_three_roots {K : Type*} [Field K]
    (P : Polynomial K) (z : Fin 3 → K) (hz : Function.Injective z)
    (hdeg : P.natDegree ≤ 2) (hzero : ∀ i, P.eval (z i) = 0) : P = 0 := by
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hz hzero
    (by simpa using Nat.lt_succ_of_le hdeg)

 theorem polynomial_zero_of_two_roots {K : Type*} [Field K]
    (P : Polynomial K) {t : K} (ht : t ≠ 0)
    (hdeg : P.natDegree ≤ 1) (hzero : P.eval 0 = 0) (htzero : P.eval t = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := ![0,t])
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> assumption
  · simpa using Nat.lt_succ_of_le hdeg

 theorem polynomial_zero_of_double_zero_and_root {K : Type*} [Field K]
    (P : Polynomial K) {t : K} (ht : t ≠ 0) (hdeg : P.natDegree ≤ 2)
    (hzero : P.eval 0 = 0) (hderiv : P.derivative.eval 0 = 0)
    (htzero : P.eval t = 0) : P = 0 := by
  obtain ⟨Q,rfl⟩ := (Polynomial.X_dvd_iff (f := P)).mpr (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hzero)
  by_cases hQ : Q = 0
  · simp [hQ]
  have hqdeg : Q.natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_mul hQ] at hdeg
    omega
  have hqzero : Q.eval 0 = 0 := by
    simpa [Polynomial.derivative_mul] using hderiv
  have hqt : Q.eval t = 0 := by
    simpa [ht] using htzero
  have := polynomial_zero_of_two_roots Q ht hqdeg hqzero hqt
  exact False.elim (hQ this)

end Nagata.Workers.W14

end
end

section

/-! Binary homogeneous root counting in the affine parameter [1:t], retaining
the point at infinity [0:1] by its top-coefficient equation. -/
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators

 def binaryAtOne (F : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => if i = 0 then 1 else Polynomial.X) F

 theorem binaryAtOne_eq_sum (F : MvPolynomial (Fin 2) ℂ) :
    binaryAtOne F = ∑ u ∈ F.support, Polynomial.C (F.coeff u) * Polynomial.X ^ u 1 := by
  classical
  rw [binaryAtOne, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro u _
  simp

 theorem binaryAtOne_eval (F : MvPolynomial (Fin 2) ℂ) (t : ℂ) :
    (binaryAtOne F).eval t = MvPolynomial.eval ![1,t] F := by
  simp [binaryAtOne_eq_sum, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]

 theorem binaryAtOne_natDegree_le {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) : (binaryAtOne F).natDegree ≤ d := by
  classical
  rw [binaryAtOne_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  apply (Polynomial.natDegree_C_mul_X_pow_le (F.coeff u) (u 1)).trans
  rw [hF.degree_eq_sum_deg_support hu]
  by_cases hz : u 1 = 0
  · simp [hz]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)

 theorem binaryAtOne_coeff_degree {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    (binaryAtOne F).coeff d = MvPolynomial.eval ![0,1] F := by
  classical
  rw [binaryAtOne_eq_sum, Polynomial.finsetSum_coeff, MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u 0 + u 1 = d := by
    have hh := hF.degree_eq_sum_deg_support hu
    change d = u.sum (fun _ n => n) at hh
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hh
    simpa [Fin.sum_univ_two] using hh.symm
  by_cases h0 : u 0 = 0
  · have h1 : u 1 = d := by omega
    simp [h0,h1]
  · have h1 : u 1 ≠ d := by omega
    simp [h0,Ne.symm h1]

 theorem binaryAtOne_eq_zero_imp {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hzero : binaryAtOne F = 0) : F = 0 := by
  have hmul : MvPolynomial.X 0 * F = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).mul hF).eq_zero_of_forall_eval_eq_zero
    intro x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases hx : x 0 = 0
    · simp [hx]
    · have hcoords : ![1, x 1 / x 0] = fun i : Fin 2 => (x 0)⁻¹ * x i := by
        funext i
        fin_cases i <;> simp [hx,div_eq_mul_inv,mul_comm]
      have hval := binaryAtOne_eval F (x 1 / x 0)
      rw [hzero, Polynomial.eval_zero, hcoords,
        Nagata.W16.homogeneous_eval_scale hF] at hval
      have hz := (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero d (inv_ne_zero hx))
      rw [hz,mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero 0)

 theorem binaryAtOne_normalized_zero {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) {a b : ℂ} (ha : a ≠ 0)
    (hz : MvPolynomial.eval ![a,b] F = 0) : (binaryAtOne F).eval (b/a) = 0 := by
  rw [binaryAtOne_eval]
  have hcoords : ![1,b/a] = fun i : Fin 2 => a⁻¹ * ![a,b] i := by
    funext i
    fin_cases i <;> simp [ha,div_eq_mul_inv,mul_comm]
  rw [hcoords,Nagata.W16.homogeneous_eval_scale hF, hz,mul_zero]

 theorem binaryAtOne_derivative (F : MvPolynomial (Fin 2) ℂ) :
    (binaryAtOne F).derivative = binaryAtOne (MvPolynomial.pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [binaryAtOne]
  | add P Q hP hQ => simpa [binaryAtOne] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    fin_cases i <;> simp_all [binaryAtOne, Polynomial.derivative_mul]
    ring

 theorem binary_zero_of_three_projective_roots {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : d ≤ 2) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : MvPolynomial.eval ![1,0] F = 0)
    (hinfty : MvPolynomial.eval ![0,1] F = 0)
    (hab : MvPolynomial.eval ![a,b] F = 0) : F = 0 := by
  apply binaryAtOne_eq_zero_imp hF
  apply polynomial_zero_of_two_roots (binaryAtOne F) (div_ne_zero hb ha)
  · have hdeg := Polynomial.natDegree_le_pred (binaryAtOne_natDegree_le hF)
      ((binaryAtOne_coeff_degree hF).trans hinfty)
    omega
  · simpa only [binaryAtOne_eval] using h0
  · exact binaryAtOne_normalized_zero hF ha hab

 theorem binary_cubic_zero_of_singular_and_three_roots {F : MvPolynomial (Fin 2) ℂ}
    (hF : F.IsHomogeneous 3) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : MvPolynomial.eval ![1,0] F = 0)
    (hinfty : MvPolynomial.eval ![0,1] F = 0)
    (hab : MvPolynomial.eval ![a,b] F = 0)
    (hsing : MvPolynomial.eval ![1,0] (MvPolynomial.pderiv 1 F) = 0) : F = 0 := by
  apply binaryAtOne_eq_zero_imp hF
  apply polynomial_zero_of_double_zero_and_root (binaryAtOne F) (div_ne_zero hb ha)
  · exact Polynomial.natDegree_le_pred (binaryAtOne_natDegree_le hF)
      ((binaryAtOne_coeff_degree hF).trans hinfty)
  · simpa only [binaryAtOne_eval] using h0
  · simpa only [binaryAtOne_derivative,binaryAtOne_eval] using hsing
  · exact binaryAtOne_normalized_zero hF ha hab

end Nagata.Workers.W14

end
end

section

noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry Nagata.W01

/-- A degree-at-most-two homogeneous equation vanishing at three distinct
points on an actual projective line contains that line as a polynomial factor. -/
theorem homogeneous_line_dvd_of_three_projective_zeros
    (L Q : MvPolynomial (Fin 3) ℂ) {d : ℕ}
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) (hQ : Q.IsHomogeneous d) (hd : d ≤ 2)
    (p : Fin 3 → PlanePoint) (hinj : Function.Injective p)
    (hLzero : ∀ i, MvPolynomial.eval (p i).rep L = 0)
    (hQzero : ∀ i, MvPolynomial.eval (p i).rep Q = 0) : L ∣ Q := by
  obtain ⟨b,a,c,hb0,hb1,ha,hc,hp0,hp1,hp2,hchange⟩ :=
    exists_homogeneous_line_normalization L hL hne (p 0) (p 1) (p 2)
      (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 0) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 1) (hinj h))
      (hLzero 0) (hLzero 1) (hLzero 2)
  rw [← basisPolynomialChange_dvd_iff b L Q, hchange]
  apply coordinateLine_dvd_of_restriction_zero
  apply binary_zero_of_three_projective_roots
    (coordinateLineRestriction_homogeneous ((basisPolynomialChange_homogeneous_iff b Q d).mpr hQ))
    hd ha hc
  · rw [coordinateLineRestriction_eval]
    change MvPolynomial.eval ![1,0,0] (basisPolynomialChange b Q) = 0
    rw [basisPolynomialChange_eval_at_coordinates b Q (p 0) _ hp0]
    exact hQzero 0
  · rw [coordinateLineRestriction_eval]
    change MvPolynomial.eval ![0,1,0] (basisPolynomialChange b Q) = 0
    rw [basisPolynomialChange_eval_at_coordinates b Q (p 1) _ hp1]
    exact hQzero 1
  · rw [coordinateLineRestriction_eval]
    change MvPolynomial.eval ![a,c,0] (basisPolynomialChange b Q) = 0
    rw [basisPolynomialChange_eval_at_coordinates b Q (p 2) _ hp2]
    exact hQzero 2

end Nagata.Workers.W14

end
end

section

noncomputable section
namespace Nagata.Workers.W14
open Nagata.ProjectiveGeometry Nagata.W01

theorem homogeneous_line_dvd_cubic_of_singular_three_projective_zeros
    (L Q : MvPolynomial (Fin 3) ℂ)
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) (hQ : Q.IsHomogeneous 3)
    (p : Fin 3 → PlanePoint) (hinj : Function.Injective p)
    (hLzero : ∀ i, MvPolynomial.eval (p i).rep L = 0)
    (hQzero : ∀ i, MvPolynomial.eval (p i).rep Q = 0)
    (hsing : ∀ j, MvPolynomial.eval (p 0).rep (MvPolynomial.pderiv j Q) = 0) : L ∣ Q := by
  obtain ⟨b,a,c,hb0,hb1,ha,hc,hp0,hp1,hp2,hchange⟩ :=
    exists_homogeneous_line_normalization L hL hne (p 0) (p 1) (p 2)
      (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 0) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 1) (hinj h))
      (hLzero 0) (hLzero 1) (hLzero 2)
  rw [← basisPolynomialChange_dvd_iff b L Q, hchange]
  apply coordinateLine_dvd_of_restriction_zero
  apply binary_cubic_zero_of_singular_and_three_roots
    (coordinateLineRestriction_homogeneous ((basisPolynomialChange_homogeneous_iff b Q 3).mpr hQ))
    ha hc
  · rw [coordinateLineRestriction_eval]
    change MvPolynomial.eval ![1,0,0] (basisPolynomialChange b Q) = 0
    rw [basisPolynomialChange_eval_at_coordinates b Q (p 0) _ hp0]
    exact hQzero 0
  · rw [coordinateLineRestriction_eval]
    change MvPolynomial.eval ![0,1,0] (basisPolynomialChange b Q) = 0
    rw [basisPolynomialChange_eval_at_coordinates b Q (p 1) _ hp1]
    exact hQzero 1
  · rw [coordinateLineRestriction_eval]
    change MvPolynomial.eval ![a,c,0] (basisPolynomialChange b Q) = 0
    rw [basisPolynomialChange_eval_at_coordinates b Q (p 2) _ hp2]
    exact hQzero 2
  · apply basis_line_partial_zero_of_singular
    intro i
    rw [hb0]
    exact hsing i

end Nagata.Workers.W14

end
end

end OAI
