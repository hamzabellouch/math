import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.QuadraticJets

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets
variable {K A : Type} [Field K] [CommRing A] [Algebra K A]

lemma taylor_mul_square (ρ : A →ₐ[K] K) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ) (d f : A)
    (hf : f ∈ (RingHom.ker ρ)^2) : τ (d*f) = ρ d • τ f := by
  have hd : d - algebraMap K A (ρ d) ∈ RingHom.ker ρ := by
    simp only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have hm : (d - algebraMap K A (ρ d))*f ∈ (RingHom.ker ρ)^3 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
    exact Ideal.mul_mem_mul hd hf
  have hz := hτ hm
  change τ ((d-algebraMap K A (ρ d))*f) = 0 at hz
  calc
    τ (d*f) = τ ((ρ d) • f) := by
      rw [Algebra.smul_def (ρ d) f]
      simpa only [sub_mul, map_sub, sub_eq_zero] using hz
    _ = _ := map_smul τ (ρ d) f

lemma discriminant_smul (c : K) (f : JetAlgebra (Fin 2) K 3) :
    discriminant (c • f) = c^2 * discriminant f := by
  simp only [discriminant, map_smul, smul_eq_mul]
  ring

lemma discriminant_quadratic (a b c : K) :
    discriminant (Ideal.Quotient.mk _
      (C a * (X 0 : MvPolynomial (Fin 2) K)^2 + C b * X 0 * X 1 + C c * (X 1 : MvPolynomial (Fin 2) K)^2)) =
      b^2 - 4*a*c := by
  have h20ne02 : exponent20 ≠ exponent02 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp [exponent20, exponent02] at this
  have h11ne20 : exponent11 ≠ exponent20 := by
    intro h
    have := DFunLike.congr_fun h 1
    simp [exponent11, exponent20] at this
  have h11ne02 : exponent11 ≠ exponent02 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp [exponent11, exponent02] at this
  have hXX : (X 0 : MvPolynomial (Fin 2) K) * X 1 = monomial exponent11 1 := by
    rw [X, X, monomial_mul_monomial]
    simp [exponent11]
  let p : MvPolynomial (Fin 2) K := C a * X 0^2 + C b * X 0 * X 1 + C c * X 1^2
  change (p.coeff exponent11)^2 - 4*p.coeff exponent20*p.coeff exponent02 = _
  dsimp only [p]
  simp only [mul_assoc (C b), hXX, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    coeff_C_mul, coeff_X_pow, coeff_monomial]
  simp only [show Finsupp.single (0 : Fin 2) 2 = exponent20 from rfl,
    show Finsupp.single (1 : Fin 2) 2 = exponent02 from rfl]
  simp [h20ne02, h20ne02.symm, h11ne20, h11ne20.symm, h11ne02, h11ne02.symm]

theorem quadratic_coefficients_nondegenerate
    (ρ : A →ₐ[K] K) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
    (x y f d a b c : A) (hx : ρ x = 0) (hy : ρ y = 0)
    (hxf : τ x = Ideal.Quotient.mk _ (X 0))
    (hyf : τ y = Ideal.Quotient.mk _ (X 1))
    (hf : f ∈ (RingHom.ker ρ)^2) (hd : ρ d ≠ 0)
    (hdf : d*f = a*x^2 + b*x*y + c*y^2)
    (hdisc : discriminant (τ f) ≠ 0) :
    (ρ b)^2 - 4*ρ a*ρ c ≠ 0 := by
  have hxx : x^2 ∈ (RingHom.ker ρ)^2 := by
    rw [pow_two, pow_two]
    exact Ideal.mul_mem_mul hx hx
  have hxy : x*y ∈ (RingHom.ker ρ)^2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  have hyy : y^2 ∈ (RingHom.ker ρ)^2 := by
    rw [pow_two, pow_two]
    exact Ideal.mul_mem_mul hy hy
  have heq := congrArg τ hdf
  rw [taylor_mul_square ρ τ hτ d f hf, map_add, map_add,
    taylor_mul_square ρ τ hτ a (x^2) hxx, mul_assoc b x y,
    taylor_mul_square ρ τ hτ b (x*y) hxy, taylor_mul_square ρ τ hτ c (y^2) hyy,
    map_pow, map_pow, map_mul, hxf, hyf] at heq
  have heq' : ρ d • τ f = Ideal.Quotient.mk _
      (C (ρ a)*(X 0 : MvPolynomial (Fin 2) K)^2 + C (ρ b)*X 0*X 1 + C (ρ c)*X 1^2) := by
    have hq (k : K) (p : MvPolynomial (Fin 2) K) :
        k • Ideal.Quotient.mk ((idealOfVars (Fin 2) K)^3) p =
        Ideal.Quotient.mk _ (C k * p) := by
      change k • (Ideal.Quotient.mkₐ K ((idealOfVars (Fin 2) K)^3)) p =
        (Ideal.Quotient.mkₐ K ((idealOfVars (Fin 2) K)^3)) (C k * p)
      rw [← MvPolynomial.smul_eq_C_mul]
      exact (map_smul (Ideal.Quotient.mkₐ K ((idealOfVars (Fin 2) K)^3)) k p).symm
    rw [heq]
    simp only [← map_pow, ← map_mul, hq, ← map_add, mul_assoc]
  have hdsc := congrArg discriminant heq'
  rw [discriminant_smul, discriminant_quadratic] at hdsc
  rw [← hdsc]
  exact mul_ne_zero (pow_ne_zero _ hd) hdisc

end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
