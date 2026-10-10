import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.FormalEtale
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticSubsystem

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.Projective

variable {K A σ : Type} [Field K] [CommRing A] [Algebra K A] [Fintype σ]

def quarticValue (a : Option σ → A) (j : QuarticIndex σ) : A :=
  a (some j.1) * a (some j.2.1) * a j.2.2.1 * a j.2.2.2

def quarticCombination (a : Option σ → A) (v : QuarticIndex σ → K) : A :=
  ∑ j, v j • quarticValue a j

def exponent20 : Fin 2 →₀ ℕ := Finsupp.single 0 2
def exponent11 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 1
def exponent02 : Fin 2 →₀ ℕ := Finsupp.single 1 2

lemma degree20 : exponent20.degree < 3 := by simp [exponent20]
lemma degree11 : exponent11.degree < 3 := by simp [exponent11]
lemma degree02 : exponent02.degree < 3 := by simp [exponent02]

def jet20 : JetAlgebra (Fin 2) K 3 →ₗ[K] K :=
  (LinearMap.proj ⟨exponent20, degree20⟩).comp (polynomialJetEquiv 3).toLinearMap
def jet11 : JetAlgebra (Fin 2) K 3 →ₗ[K] K :=
  (LinearMap.proj ⟨exponent11, degree11⟩).comp (polynomialJetEquiv 3).toLinearMap
def jet02 : JetAlgebra (Fin 2) K 3 →ₗ[K] K :=
  (LinearMap.proj ⟨exponent02, degree02⟩).comp (polynomialJetEquiv 3).toLinearMap

def discriminant (f : JetAlgebra (Fin 2) K 3) : K :=
  jet11 f ^ 2 - 4 * jet20 f * jet02 f

def coefficientForm (a : Option σ → A) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (l : JetAlgebra (Fin 2) K 3 →ₗ[K] K) : MvPolynomial (QuarticIndex σ) K :=
  ∑ j, C (l (τ (quarticValue a j))) * X j

def discriminantPolynomial (a : Option σ → A) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3) :
    MvPolynomial (QuarticIndex σ) K :=
  coefficientForm a τ jet11 ^ 2 - 4 * coefficientForm a τ jet20 * coefficientForm a τ jet02

lemma coefficientForm_eval (a : Option σ → A) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (l : JetAlgebra (Fin 2) K 3 →ₗ[K] K) (v : QuarticIndex σ → K) :
    aeval v (coefficientForm a τ l) = l (τ (quarticCombination a v)) := by
  simp [coefficientForm, quarticCombination, map_sum, mul_comm, smul_eq_mul]

lemma discriminantPolynomial_eval (a : Option σ → A) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (v : QuarticIndex σ → K) :
    aeval v (discriminantPolynomial a τ) = discriminant (τ (quarticCombination a v)) := by
  simp only [discriminantPolynomial, map_sub, map_pow, map_mul, map_ofNat,
    coefficientForm_eval, discriminant]

lemma quarticCombination_add (a : Option σ → A) (v w : QuarticIndex σ → K) :
    quarticCombination a (v + w) = quarticCombination a v + quarticCombination a w := by
  simp [quarticCombination, add_smul, Finset.sum_add_distrib]

lemma quarticCombination_single [DecidableEq σ] (a : Option σ → A) (j : QuarticIndex σ) (c : K) :
    quarticCombination a (Pi.single j c) = c • quarticValue a j := by
  classical
  simp [quarticCombination, Pi.single_apply, ite_smul]

lemma discriminant_squares :
    discriminant (K := K) (Ideal.Quotient.mk _ ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2)) = -4 := by
  have h01 : (Finsupp.single (0 : Fin 2) 2 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 2 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  have h11a : exponent11 ≠ exponent20 := by
    intro h
    have := DFunLike.congr_fun h 1
    simp [exponent11, exponent20] at this
  have h11b : exponent11 ≠ exponent02 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp [exponent11, exponent02] at this
  change (((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2).coeff exponent11)^2 -
    4 * ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2).coeff exponent20 *
      ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2).coeff exponent02 = -4
  change exponent11 ≠ Finsupp.single 0 2 at h11a
  change exponent11 ≠ Finsupp.single 1 2 at h11b
  simp [AddMonoidAlgebra.coeff_add, coeff_X_pow, exponent20, exponent02,
    h01, h01.symm, Ne.symm h11a, Ne.symm h11b]

lemma discriminantPolynomial_ne_zero [CharZero K]
    (a : Option σ → A) (h0 : a none = 1) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (i j : σ)
    (hi : τ (a (some i)) = -Ideal.Quotient.mk _ (X 0))
    (hj : τ (a (some j)) = -Ideal.Quotient.mk _ (X 1)) :
    discriminantPolynomial a τ ≠ 0 := by
  classical
  let v : QuarticIndex σ → K := Pi.single (i,i,none,none) 1 + Pi.single (j,j,none,none) 1
  have hv : τ (quarticCombination a v) =
      Ideal.Quotient.mk _ ((X 0 : MvPolynomial (Fin 2) K)^2 + X 1^2) := by
    simp only [v, quarticCombination_add, quarticCombination_single, one_smul,
      quarticValue, h0, mul_one, map_add, map_mul, hi, hj]
    simp only [map_pow]
    ring
  intro hz
  have hh := discriminantPolynomial_eval a τ v
  rw [hz, map_zero, hv, discriminant_squares] at hh
  norm_num at hh

lemma quarticCombination_mem_square (a : Option σ → A) (ρ : A →ₐ[K] K)
    (ha : ∀ i : σ, ρ (a (some i)) = 0) (v : QuarticIndex σ → K) :
    quarticCombination a v ∈ (RingHom.ker ρ)^2 := by
  apply Ideal.sum_mem
  intro j hj
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_left
  apply Ideal.mul_mem_right
  apply Ideal.mul_mem_right
  rw [pow_two]
  exact Ideal.mul_mem_mul (ha j.1) (ha j.2.1)

omit [Fintype σ] in
theorem exists_quadratic_jet_of_etale (a : Option σ → A) (ρ : A →ₐ[K] K)
    (ha : ∀ i : σ, ρ (a (some i)) = 0) (i : Fin 2 → σ)
    (het : (eval₂Hom (algebraMap K A) (fun j => -a (some (i j)))).Etale) :
    ∃ τ : A →ₐ[K] JetAlgebra (Fin 2) K 3,
      RingHom.ker τ = (RingHom.ker ρ)^3 ∧
      (∀ f : A, jetAugment 3 (by decide) (τ f) = ρ f) ∧
      ∀ j : Fin 2, τ (a (some (i j))) = -Ideal.Quotient.mk _ (X j) := by
  let : Algebra (MvPolynomial (Fin 2) K) A :=
    (eval₂Hom (algebraMap K A) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) A :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (algebraMap K A) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) K) A := het
  obtain ⟨τ, hτ, hc⟩ := exists_regular_taylor (σ := Fin 2) (F := K) (S := A) 3 (by decide)
  refine ⟨specializeTaylor 3 τ ρ,
    regularTaylor_detects_ideal_power 3 (by decide) τ hτ hc ρ,
    specializeTaylor_augment 3 (by decide) τ hτ ρ, ?_⟩
  intro j
  have hh := DFunLike.congr_fun (specializeTaylor_coordinate 3 τ hc ρ) (X j)
  change specializeTaylor 3 τ ρ ((algebraMap (MvPolynomial (Fin 2) K) A) (X j)) =
    Ideal.Quotient.mk _ (aeval (fun b => X b + C
      (ρ ((algebraMap (MvPolynomial (Fin 2) K) A) (X b)))) (X j)) at hh
  simp only [aeval_X, RingHom.algebraMap_toAlgebra, eval₂Hom_X', map_neg, ha,
    neg_zero, C_0, add_zero] at hh
  simpa only [map_neg, neg_neg] using congrArg Neg.neg hh

end
end MaximalSeshadri.QuadraticJets

end


end
end

end OAI
