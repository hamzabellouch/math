import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundedAssociativeBCH
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponentialNaturality

namespace OAI

/-! # The universal product formula in faithful unipotent coordinates

This algebraic transport uses only the exponential compatibility of the given
representation. Its bound may be enlarged, so two coordinate models can use
exactly the same coefficients.
-/

noncomputable section
namespace PolycyclicRecognition

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type*} [LieRing L] [LieAlgebra ℝ L] [Group L]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem finite_product_of_unipotent_coordinates
    (ρ : L →* Aˣ) (hρ : Function.Injective ρ) (j : L →ₗ⁅ℝ⁆ A)
    (hexp : ∀ x, ρ x = algebraExpUnit (j x)) (c : ℕ)
    (hc : ∀ l : List L, c < l.length → (l.map j).prod = 0)
    {n : ℕ} (X : Fin n → L) :
    (List.ofFn X).prod = finiteDynkinPolynomial (universalDynkinCoefficients c n) X := by
  have hw (w : FreeMonoid (Fin n)) (h : c < w.length) :
      FreeMonoid.lift (fun i => j (X i)) w = 0 := by
    have hh := hc (w.toList.map X) (by simpa only [List.length_map, FreeMonoid.length] using h)
    simpa only [List.map_map, FreeMonoid.lift_apply, Function.comp_def] using hh
  have hn (i : Fin n) : IsNilpotent (j (X i)) :=
    ⟨c + 1, nilpotent_word_letter_pow (fun i => j (X i)) hw i⟩
  have hnp : IsNilpotent
      (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) := by
    rw [universalDynkinPolynomial_eq]
    exact ⟨c + 1, finiteUniversalLiePolynomial_pow (fun i => j (X i)) hw⟩
  apply hρ
  apply Units.ext
  calc
    (ρ (List.ofFn X).prod : A) = (List.ofFn (fun i => (ρ (X i) : A))).prod := by
      exact (map_list_prod ((Units.coeHom A).comp ρ) _).trans
        (congrArg List.prod (List.map_ofFn ..))
    _ = (List.ofFn (fun i => IsNilpotent.exp (j (X i)))).prod := by
      congr 1
      apply congrArg List.ofFn
      funext i
      rw [hexp, coe_algebraExpUnit]
      exact analytic_exp_eq_nilpotent_exp (hn i)
    _ = IsNilpotent.exp
        (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) :=
      bounded_associative_bch _ hw
    _ = (ρ (finiteDynkinPolynomial (universalDynkinCoefficients c n) X) : A) := by
      rw [hexp, coe_algebraExpUnit]
      rw [finiteDynkinPolynomial_map, analytic_exp_eq_nilpotent_exp hnp]

end PolycyclicRecognition

end

end OAI
