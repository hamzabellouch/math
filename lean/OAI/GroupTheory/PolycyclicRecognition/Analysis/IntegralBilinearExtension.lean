import OAI.GroupTheory.PolycyclicRecognition.Lattices.BilinearCentralLattice
import Mathlib.Tactic.Ring

namespace OAI

/-! # Extending an integral two-step law to a real Lie group -/

noncomputable section
namespace PolycyclicRecognition

variable {d e : ℕ}

def coefficientBilinear {R : Type*} [CommRing R]
    (a : Fin e → Fin d → Fin d → R) :
    (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin e → R) :=
  LinearMap.mk₂ R (fun x y k => ∑ i, ∑ j, a k i j * x i * y j)
    (by intros; ext k; simp [add_mul, mul_add, Finset.sum_add_distrib])
    (by
      intro r x y
      ext k
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring)
    (by intros; ext k; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro r x y
      ext k
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring)

def integerVectorMap (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℝ) where
  toFun x i := (x i : ℝ)
  map_zero' := by ext i; exact Int.cast_zero
  map_add' x y := by ext i; exact Int.cast_add _ _

theorem integerVectorMap_injective (n : ℕ) : Function.Injective (integerVectorMap n) := by
  intro x y h
  ext i
  have hi : (x i : ℝ) = (y i : ℝ) := congrFun h i
  exact_mod_cast hi

theorem integerVectorMap_mem (n : ℕ) (x : Fin n → ℤ) :
    integerVectorMap n x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))) := by
  apply ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨x i, rfl⟩

theorem exists_integerVectorMap_of_mem (n : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) :
    ∃ z, integerVectorMap n z = x := by
  have h := ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x).mp hx
  choose z hz using h
  exact ⟨z, funext hz⟩

def realCoefficientBilinear (a : Fin e → Fin d → Fin d → ℤ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin e → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (coefficientBilinear (fun k i j => (a k i j : ℝ))))

theorem realCoefficientBilinear_cast (a : Fin e → Fin d → Fin d → ℤ)
    (x y : Fin d → ℤ) :
    realCoefficientBilinear a (integerVectorMap d x) (integerVectorMap d y) =
      integerVectorMap e (coefficientBilinear a x y) := by
  ext k
  change (∑ i, ∑ j, (a k i j : ℝ) * (x i : ℝ) * (y j : ℝ)) =
    ((∑ i, ∑ j, a k i j * x i * y j : ℤ) : ℝ)
  simp

theorem realCoefficientBilinear_integral (a : Fin e → Fin d → Fin d → ℤ) :
    ∀ x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))),
      ∀ y ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))),
        realCoefficientBilinear a x y ∈
          Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin e))) := by
  intro x hx y hy
  obtain ⟨u, rfl⟩ := exists_integerVectorMap_of_mem d x hx
  obtain ⟨v, rfl⟩ := exists_integerVectorMap_of_mem d y hy
  rw [realCoefficientBilinear_cast]
  exact integerVectorMap_mem e _

end PolycyclicRecognition

end

end OAI
