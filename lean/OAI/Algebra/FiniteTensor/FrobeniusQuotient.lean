import Mathlib

namespace OAI

/-! Polynomial Frobenius quotients, bounded coefficients, residues and derivatives. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
namespace FrobeniusTruncation
noncomputable section

variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)

def ideal : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range (fun i : σ => (MvPolynomial.X i : MvPolynomial σ K) ^ p))

abbrev Ring := MvPolynomial σ K ⧸ ideal K σ p

def coord (i : σ) : Ring K σ p :=
  Ideal.Quotient.mk (ideal K σ p) (MvPolynomial.X i)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem variable_pow (i : σ) : coord K σ p i ^ p = 0 := by
  rw [coord, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

omit [Fintype σ] [DecidableEq σ] in
private theorem ideal_as_monomials : ideal K σ p =
    Ideal.span ((fun a : σ →₀ ℕ => MvPolynomial.monomial a (1 : K)) ''
      Set.range (fun i : σ => Finsupp.single i p)) := by
  unfold ideal
  congr 1
  ext f
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Finsupp.single i p, ⟨i, rfl⟩, (MvPolynomial.X_pow_eq_monomial).symm⟩
  · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, MvPolynomial.X_pow_eq_monomial⟩

 
def socleExponent : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => p - 1)

omit [DecidableEq σ] in
@[simp] theorem socleExponent_apply (i : σ) : socleExponent σ p i = p - 1 := by
  simp [socleExponent]

 
omit [Fintype σ] [DecidableEq σ] in
theorem coeff_zero_of_mem_ideal (a : σ →₀ ℕ) (ha : ∀ i, a i < p)
    (f : MvPolynomial σ K) (hf : f ∈ ideal K σ p) : f.coeff a = 0 := by
  by_contra h
  rw [ideal_as_monomials, MvPolynomial.mem_ideal_span_monomial_image] at hf
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hf a (MvPolynomial.mem_support_iff.mpr h)
  have hpi : p ≤ a i := by simpa using hi i
  exact (not_le_of_gt (ha i)) hpi

 
def residue (hp : 0 < p) : Ring K σ p →ₗ[K] K :=
  ((ideal K σ p).restrictScalars K).liftQ (MvPolynomial.lcoeff K (socleExponent σ p))
    (by
      intro f hf
      exact coeff_zero_of_mem_ideal K σ p (socleExponent σ p)
        (fun i => by simp only [socleExponent_apply]; omega) f hf)

omit [DecidableEq σ] in
@[simp] theorem residue_mk (hp : 0 < p) (f : MvPolynomial σ K) :
    residue K σ p hp (Ideal.Quotient.mk (ideal K σ p) f) =
      f.coeff (socleExponent σ p) := rfl

@[simp] theorem residue_socle (hp : 0 < p) :
    residue K σ p hp (Ideal.Quotient.mk (ideal K σ p)
      (MvPolynomial.monomial (socleExponent σ p) 1)) = 1 := by
  simp

 
theorem socle_ne_zero (hp : 0 < p) :
    Ideal.Quotient.mk (ideal K σ p) (MvPolynomial.monomial (socleExponent σ p) 1) ≠ 0 := by
  intro h
  have he := residue_socle K σ p hp
  rw [h, map_zero] at he
  exact zero_ne_one he

variable [CharP K p]

 
omit [Fintype σ] [DecidableEq σ] in
theorem pderiv_mem (i : σ) (f : MvPolynomial σ K) (hf : f ∈ ideal K σ p) :
    MvPolynomial.pderiv i f ∈ ideal K σ p := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    simp only [MvPolynomial.pderiv_pow, CharP.cast_eq_zero, zero_mul]
    exact Ideal.zero_mem _
  | zero => simp
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (ideal K σ p).add_mem ihf ihg
  | smul a f hf ih =>
    rw [smul_eq_mul, MvPolynomial.pderiv_mul]
    exact (ideal K σ p).add_mem ((ideal K σ p).mul_mem_left _ hf)
      ((ideal K σ p).mul_mem_left _ ih)

 

def derivative (i : σ) : Ring K σ p →ₗ[K] Ring K σ p :=
  ((ideal K σ p).restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K (ideal K σ p)).toLinearMap.comp
      (MvPolynomial.pderiv i).toLinearMap)
    (by
      intro f hf
      change Ideal.Quotient.mk (ideal K σ p) (MvPolynomial.pderiv i f) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (pderiv_mem K σ p i f hf))

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem derivative_mk (i : σ) (f : MvPolynomial σ K) :
    derivative K σ p i (Ideal.Quotient.mk (ideal K σ p) f) =
      Ideal.Quotient.mk (ideal K σ p) (MvPolynomial.pderiv i f) := rfl

 
omit [DecidableEq σ] in
theorem residue_derivative (hp : 0 < p) (i : σ) (f : Ring K σ p) :
    residue K σ p hp (derivative K σ p i f) = 0 := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  rw [derivative_mk, residue_mk, MvPolynomial.coeff_pderiv, socleExponent_apply]
  have hn : p - 1 + 1 = p := by omega
  rw [← Nat.cast_add_one, hn, CharP.cast_eq_zero, mul_zero]

 
omit [Fintype σ] [DecidableEq σ] in
theorem derivative_mul (i : σ) (f g : Ring K σ p) :
    derivative K σ p i (f * g) = derivative K σ p i f * g + f * derivative K σ p i g := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
  rw [← map_mul, derivative_mk, MvPolynomial.pderiv_mul]
  simp

 
omit [Fintype σ] in
theorem polynomial_pderiv_commute (i j : σ) (f : MvPolynomial σ K) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  by_cases hij : i = j
  · subst j; rfl
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f k hf =>
    by_cases hi : k = i <;> by_cases hj : k = j <;>
      simp [MvPolynomial.pderiv_X, hi, hj, hij, Ne.symm hij, eq_comm, hf] <;> ring

 

omit [Fintype σ] in
theorem derivative_commute (i j : σ) (f : Ring K σ p) :
    derivative K σ p i (derivative K σ p j f) =
      derivative K σ p j (derivative K σ p i f) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
  simp only [derivative_mk, polynomial_pderiv_commute K σ]

variable [Fact p.Prime]

 
omit [Fintype σ] [DecidableEq σ] in
theorem frobenius_mk (f : MvPolynomial σ K) :
    (Ideal.Quotient.mk (ideal K σ p) f)^p =
      algebraMap K (Ring K σ p) ((MvPolynomial.constantCoeff f)^p) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.constantCoeff_C]
    change (algebraMap K (Ring K σ p) a)^p = _
    exact (map_pow _ _ _).symm
  | add f g hf hg =>
    rw [← map_pow, add_pow_char, map_add, map_pow, map_pow, hf, hg]
    simp [add_pow_char]
  | mul_X f i hf =>
    rw [map_mul, mul_pow]
    change _ * coord K σ p i ^ p = _
    rw [variable_pow, mul_zero]
    simp [zero_pow (Fact.out : p.Prime).ne_zero]

end
end FrobeniusTruncation
end PD4Tensor
end

end OAI
