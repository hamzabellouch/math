import Mathlib

namespace OAI

section
namespace ElementaryPositivity.SymbolCoordinates
open MvPolynomial
variable {σ A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def coefficientMap (l : A →ₗ[ℚ] ℚ) :
    MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ ℚ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap l).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

@[simp] lemma coeff_coefficientMap (l : A →ₗ[ℚ] ℚ) (f : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (coefficientMap l f).coeff m=l (f.coeff m) := rfl

lemma coefficientMap_scalar_mul (l : A →ₗ[ℚ] ℚ) (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    coefficientMap l (MvPolynomial.map (algebraMap ℚ A) p * f) = p * coefficientMap l f := by
  classical
  ext m
  simp only [coeff_coefficientMap,coeff_mul,coeff_map,map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simpa [Algebra.smul_def,smul_eq_mul] using
    l.map_smul (p.coeff x.1) (f.coeff x.2)

variable {ι : Type*} (b : Module.Basis ι ℚ A)

noncomputable def coordinate (i : ι) : MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ ℚ :=
  coefficientMap ((Finsupp.lapply i).comp b.repr.toLinearMap)

@[simp] lemma coeff_coordinate (i : ι) (f : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (coordinate b i f).coeff m=b.repr (f.coeff m) i := rfl

lemma coordinate_scalar_mul (i : ι) (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    coordinate b i (MvPolynomial.map (algebraMap ℚ A) p * f) = p * coordinate b i f :=
  coefficientMap_scalar_mul _ _ _

lemma coordinates_detect (f : MvPolynomial σ A) (h : ∀ i,coordinate b i f=0) : f=0 := by
  ext m
  apply b.repr.injective
  ext i
  have hh:=congrArg (fun polynomial : MvPolynomial σ ℚ => polynomial.coeff m) (h i)
  simpa using hh

noncomputable def coordinateSupport (f : MvPolynomial σ A) : Finset ι := by
  classical
  exact f.support.biUnion (fun m=>(b.repr (f.coeff m)).support)

lemma coordinate_support_subset (f : MvPolynomial σ A) (m : σ →₀ ℕ) :
    (b.repr (f.coeff m)).support ⊆ coordinateSupport b f := by
  classical
  intro i hi
  by_cases hm : m∈f.support
  · exact Finset.mem_biUnion.mpr ⟨m,hm,hi⟩
  · have hzero:=notMem_support_iff.mp hm
    simp [hzero] at hi

lemma reconstruct (f : MvPolynomial σ A) :
    (∑ i ∈ coordinateSupport b f,C (b i)*MvPolynomial.map (algebraMap ℚ A) (coordinate b i f))=f := by
  classical
  ext m
  simp only [coeff_sum,coeff_C_mul,coeff_map,coeff_coordinate]
  calc
    (∑ i ∈ coordinateSupport b f,b i * algebraMap ℚ A (b.repr (f.coeff m) i)) =
        ∑ i ∈ (b.repr (f.coeff m)).support,b.repr (f.coeff m) i • b i := by
      simp only [Algebra.smul_def,mul_comm]
      exact (Finset.sum_subset (coordinate_support_subset b f m) (by
        intro i hi hni
        simp [Finsupp.notMem_support_iff.mp hni])).symm
    _ = f.coeff m := b.linearCombination_repr _

theorem scalar_mul_eq_zero_iff (p : MvPolynomial σ ℚ) (hp : p≠0) (f : MvPolynomial σ A) :
    MvPolynomial.map (algebraMap ℚ A) p * f=0 ↔ f=0 := by
  constructor
  · intro hf
    apply coordinates_detect (Module.Free.chooseBasis ℚ A)
    intro i
    have h:=congrArg (coordinate (Module.Free.chooseBasis ℚ A) i) hf
    rw [coordinate_scalar_mul,map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hp
  · rintro rfl
    exact mul_zero _

theorem scalar_dvd_iff (p : MvPolynomial σ ℚ) (f : MvPolynomial σ A) :
    MvPolynomial.map (algebraMap ℚ A) p ∣ f ↔ ∀ i,p ∣ coordinate b i f := by
  classical
  constructor
  · rintro ⟨g,rfl⟩ i
    rw [coordinate_scalar_mul]
    exact dvd_mul_right p _
  · intro h
    choose g hg using h
    refine ⟨∑ i ∈ coordinateSupport b f,C (b i)*MvPolynomial.map (algebraMap ℚ A) (g i),?_⟩
    calc
      f = ∑ i ∈ coordinateSupport b f,C (b i)*MvPolynomial.map (algebraMap ℚ A) (coordinate b i f) :=
        (reconstruct b f).symm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hg i,map_mul]
        ring

end ElementaryPositivity.SymbolCoordinates

namespace ElementaryPositivity.CenterCalculus
open MvPolynomial ElementaryPositivity.SymbolCoordinates
variable {A σ : Type*} [CommRing A] [Algebra ℚ A]

theorem product_dvd_of_scalar_factors {κ : Type*} (s : Finset κ)
    (p : κ → MvPolynomial σ ℚ) (q : MvPolynomial σ A)
    (hrel : (s : Set κ).Pairwise (fun i j => IsRelPrime (p i) (p j)))
    (h : ∀ i∈s, map (algebraMap ℚ A) (p i) ∣ q) :
    map (algebraMap ℚ A) (∏ i∈s,p i) ∣ q := by
  let b := Module.Free.chooseBasis ℚ A
  apply (scalar_dvd_iff b _ q).mpr
  intro k
  apply Finset.prod_dvd_of_isRelPrime hrel
  intro i hi
  exact (scalar_dvd_iff b (p i) q).mp (h i hi) k

theorem scalar_mul_eq_zero (p : MvPolynomial σ ℚ) (hp : p≠0)
    (q : MvPolynomial σ A) (h : map (algebraMap ℚ A) p*q=0) : q=0 :=
  (scalar_mul_eq_zero_iff p hp q).mp h

theorem scalar_mul_injective (p : MvPolynomial σ ℚ) (hp : p≠0) :
    Function.Injective (fun q : MvPolynomial σ A=>map (algebraMap ℚ A) p*q) := by
  intro q r h
  dsimp only at h
  apply sub_eq_zero.mp
  apply scalar_mul_eq_zero p hp
  rw [mul_sub,h,sub_self]

end ElementaryPositivity.CenterCalculus

end

end OAI
