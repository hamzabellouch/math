import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Cotangent
import OAI.NumberTheory.SiegelZeros.Structure.Augmentation

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.W25

open MvPolynomial
open scoped Classical
variable {σ K : Type*} [Fintype σ] [Field K]

abbrev Active (t : σ → ℕ) := {i : σ // 0 < t i}

def activeBoxIndex (t : σ → ℕ) (j : Active t) : Box t := by
  classical
  exact fun i => ⟨(Finsupp.single j.val 1 : σ →₀ ℕ) i, by
    by_cases h : i = j.val
    · subst i
      simpa using Nat.succ_lt_succ j.property
    · simp [h]⟩

@[simp] theorem boxExponent_activeBoxIndex (t : σ → ℕ) (j : Active t) :
    boxExponent t (activeBoxIndex t j) = Finsupp.single j.val 1 := by
  ext i
  rfl

def quotientFirstCoefficient (t : σ → ℕ) (j : Active t) :
    (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) →ₗ[K] K :=
  (LinearMap.proj (activeBoxIndex t j)).comp
    (truncatedQuotientEquiv (K := K) t).toLinearMap

@[simp] theorem quotientFirstCoefficient_mk (t : σ → ℕ) (j : Active t)
    (p : MvPolynomial σ K) :
    quotientFirstCoefficient (K := K) t j (Ideal.Quotient.mk (truncationIdeal (K := K) t) p) =
      p.coeff (Finsupp.single j.val 1) := by
  change p.coeff (boxExponent t (activeBoxIndex t j)) = _
  rw [boxExponent_activeBoxIndex]

theorem quotientFirstCoefficient_eq_zero_of_mem_square (t : σ → ℕ) (j : Active t)
    (x : MvPolynomial σ K ⧸ truncationIdeal (K := K) t)
    (hx : x ∈ augmentationIdeal (K := K) t ^ 2) :
    quotientFirstCoefficient (K := K) t j x = 0 := by
  rw [augmentationIdeal_eq_map, ← Ideal.map_pow] at hx
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (truncationIdeal (K := K) t)) Ideal.Quotient.mk_surjective).mp hx
  rw [quotientFirstCoefficient_mk]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' 2 p).mp hp
    (Finsupp.single j.val 1) (by simp)

theorem mem_augmentationSquare_of_coefficients_zero (t : σ → ℕ)
    (x : MvPolynomial σ K ⧸ truncationIdeal (K := K) t)
    (hconstant : augmentation (K := K) t x = 0)
    (hfirst : ∀ j : Active t, quotientFirstCoefficient (K := K) t j x = 0) :
    x ∈ augmentationIdeal (K := K) t ^ 2 := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hc : p.coeff 0 = 0 := hconstant
  have hf : ∀ j : Active t, p.coeff (Finsupp.single j.val 1) = 0 := by
    simpa only [quotientFirstCoefficient_mk] using hfirst
  rw [MvPolynomial.as_sum p, map_sum]
  apply Ideal.sum_mem
  intro m hm
  by_cases hdegree : 2 ≤ Finsupp.degree m
  · rw [augmentationIdeal_eq_map, ← Ideal.map_pow]
    apply Ideal.mem_map_of_mem
    exact (MvPolynomial.monomial_mem_pow_idealOfVars_iff 2 m
      (MvPolynomial.mem_support_iff.mp hm)).mpr hdegree
  · have hd : Finsupp.degree m = 0 ∨ Finsupp.degree m = 1 := by omega
    rcases hd with hd | hd
    · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hd
      rw [hm0, hc, monomial_zero, map_zero]
      exact Ideal.zero_mem _
    · obtain ⟨i, hmi⟩ : ∃ i, Finsupp.single i 1 = m := by
        have hmem : m ∈ ({d : σ →₀ ℕ | Finsupp.degree d = 1} : Set (σ →₀ ℕ)) := hd
        rw [← Finsupp.range_single_one] at hmem
        exact hmem
      subst m
      by_cases hi : 0 < t i
      · rw [hf ⟨i, hi⟩, monomial_zero, map_zero]
        exact Ideal.zero_mem _
      · have hti : t i = 0 := Nat.eq_zero_of_not_pos hi
        have hXi : (X i : MvPolynomial σ K) ∈ truncationIdeal (K := K) t := by
          have hgen : (X i : MvPolynomial σ K) ^ (t i + 1) ∈ truncationIdeal (K := K) t :=
            Ideal.subset_span ⟨i, rfl⟩
          simpa only [hti, zero_add, pow_one] using hgen
        have hmono : monomial (Finsupp.single i 1)
            (p.coeff (Finsupp.single i 1)) ∈ truncationIdeal (K := K) t := by
          rw [← MvPolynomial.C_mul_X_pow_eq_monomial, pow_one]
          exact Ideal.mul_mem_left _ _ hXi
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmono]
        exact Ideal.zero_mem _

theorem mem_augmentationSquare_iff (t : σ → ℕ)
    (x : MvPolynomial σ K ⧸ truncationIdeal (K := K) t) :
    x ∈ augmentationIdeal (K := K) t ^ 2 ↔
      augmentation (K := K) t x = 0 ∧
        ∀ j : Active t, quotientFirstCoefficient (K := K) t j x = 0 := by
  constructor
  · intro hx
    exact ⟨Ideal.pow_le_self (by decide : 2 ≠ 0) hx,
      fun j => quotientFirstCoefficient_eq_zero_of_mem_square (K := K) t j x hx⟩
  · rintro ⟨hc, hf⟩
    exact mem_augmentationSquare_of_coefficients_zero (K := K) t x hc hf

def augmentationFirstCoordinates (t : σ → ℕ) :
    augmentationIdeal (K := K) t →ₗ[K] (Active t → K) :=
  LinearMap.pi fun j => (quotientFirstCoefficient (K := K) t j).comp
    ((augmentationIdeal (K := K) t).restrictScalars K).subtype

theorem augmentationFirstCoordinates_product_zero (t : σ → ℕ)
    (x y : augmentationIdeal (K := K) t) :
    augmentationFirstCoordinates (K := K) t (x*y) = 0 := by
  ext j
  change quotientFirstCoefficient (K := K) t j ((x : MvPolynomial σ K ⧸ truncationIdeal (K := K) t) * y) = 0
  exact quotientFirstCoefficient_eq_zero_of_mem_square (K := K) t j _
    (by simpa only [pow_two] using (Ideal.mul_mem_mul x.property y.property))

def rectangleCotangentCoordinates (t : σ → ℕ) :
    (augmentationIdeal (K := K) t).Cotangent →ₗ[K] (Active t → K) :=
  Ideal.Cotangent.lift (augmentationFirstCoordinates (K := K) t)
    (augmentationFirstCoordinates_product_zero (K := K) t)

@[simp] theorem rectangleCotangentCoordinates_toCotangent (t : σ → ℕ)
    (x : augmentationIdeal (K := K) t) (j : Active t) :
    rectangleCotangentCoordinates (K := K) t ((augmentationIdeal (K := K) t).toCotangent x) j =
      quotientFirstCoefficient (K := K) t j x := rfl

theorem rectangleCotangentCoordinates_injective (t : σ → ℕ) :
    Function.Injective (rectangleCotangentCoordinates (K := K) t) := by
  apply (injective_iff_map_eq_zero
    (rectangleCotangentCoordinates (K := K) t).toAddMonoidHom).mpr
  intro z hz
  obtain ⟨x, rfl⟩ := (augmentationIdeal (K := K) t).toCotangent_surjective z
  apply ((augmentationIdeal (K := K) t).toCotangent_eq_zero x).mpr
  apply mem_augmentationSquare_of_coefficients_zero (K := K) t x x.property
  intro j
  exact congrFun hz j

def coordinateCotangentClass (t : σ → ℕ) (j : Active t) :
    (augmentationIdeal (K := K) t).Cotangent :=
  (augmentationIdeal (K := K) t).toCotangent
    ⟨Ideal.Quotient.mk (truncationIdeal (K := K) t) (X j.val), by
      change augmentation (K := K) t
        (Ideal.Quotient.mk (truncationIdeal (K := K) t) (X j.val)) = 0
      simp [← MvPolynomial.constantCoeff_eq]⟩

theorem rectangleCotangentCoordinates_coordinate (t : σ → ℕ) (i j : Active t) :
    rectangleCotangentCoordinates (K := K) t (coordinateCotangentClass (K := K) t j) i =
      if i = j then (1 : K) else 0 := by
  classical
  change quotientFirstCoefficient (K := K) t i
    (Ideal.Quotient.mk (truncationIdeal (K := K) t) (X j.val)) = _
  rw [quotientFirstCoefficient_mk, MvPolynomial.coeff_X]
  simp only [Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)]
  by_cases hij : i = j
  · subst i
    simp
  · have hval : j.val ≠ i.val := fun h => hij (Subtype.ext h.symm)
    simp [hij, hval]

theorem rectangleCotangentCoordinates_surjective (t : σ → ℕ) :
    Function.Surjective (rectangleCotangentCoordinates (K := K) t) := by
  classical
  intro f
  refine ⟨∑ j : Active t, f j • coordinateCotangentClass (K := K) t j, ?_⟩
  ext i
  simp [map_sum, map_smul, rectangleCotangentCoordinates_coordinate,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]

def rectangleCotangentEquiv (t : σ → ℕ) :
    (augmentationIdeal (K := K) t).Cotangent ≃ₗ[K] (Active t → K) :=
  LinearEquiv.ofBijective (rectangleCotangentCoordinates (K := K) t)
    ⟨rectangleCotangentCoordinates_injective (K := K) t,
      rectangleCotangentCoordinates_surjective (K := K) t⟩

def rectangleCotangentBasis (t : σ → ℕ) :
    Module.Basis (Active t) K (augmentationIdeal (K := K) t).Cotangent :=
  Module.Basis.ofEquivFun (rectangleCotangentEquiv (K := K) t)

theorem rectangleCotangentBasis_eq_coordinate (t : σ → ℕ) (j : Active t) :
    rectangleCotangentBasis (K := K) t j = coordinateCotangentClass (K := K) t j := by
  classical
  rw [rectangleCotangentBasis, Module.Basis.coe_ofEquivFun]
  apply (rectangleCotangentEquiv (K := K) t).injective
  rw [LinearEquiv.apply_symm_apply]
  ext i
  change (Pi.single j (1 : K) : Active t → K) i =
    rectangleCotangentCoordinates (K := K) t (coordinateCotangentClass (K := K) t j) i
  rw [rectangleCotangentCoordinates_coordinate]
  simp [Pi.single_apply, eq_comm]

theorem coordinateCotangentClass_span (t : σ → ℕ) :
    Submodule.span K (Set.range (coordinateCotangentClass (K := K) t)) = ⊤ := by
  have hfun : (rectangleCotangentBasis (K := K) t :
      Active t → (augmentationIdeal (K := K) t).Cotangent) =
      coordinateCotangentClass (K := K) t := by
    funext j
    exact rectangleCotangentBasis_eq_coordinate t j
  rw [← hfun]
  exact (rectangleCotangentBasis (K := K) t).span_eq

theorem finrank_rectangleCotangent (t : σ → ℕ) :
    Module.finrank K (augmentationIdeal (K := K) t).Cotangent =
      Fintype.card (Active t) := by
  classical
  rw [(rectangleCotangentEquiv (K := K) t).finrank_eq, Module.finrank_pi]

end WeightedTorusJets.W25

end

end SiegelZeros

end OAI
