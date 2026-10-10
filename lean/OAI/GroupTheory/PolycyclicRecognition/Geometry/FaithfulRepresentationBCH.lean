import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundedAssociativeBCH
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponentialNaturality

namespace OAI

/-! # Transporting finite BCH through an actual faithful group representation

The derivative is the Lie homomorphism used in the polynomial. The only
algebraic assumption is a concrete common bound on products of its values.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

theorem finite_bch_of_faithful_nilpotent_representation
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      j.toLinearMap.toContinuousLinearMap)
    (c : ℕ)
    (hc : ∀ l : List (GroupLieAlgebra (𝓘(ℝ, E)) G), c < l.length → (l.map j).prod = 0)
    {n : ℕ} (X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G) :
    (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial (universalDynkinCoefficients c n) X) := by
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
    (ρ (List.ofFn (fun i => Exp (X i))).prod : A) =
        (List.ofFn (fun i => (ρ (Exp (X i)) : A))).prod := by
      exact (map_list_prod ((Units.coeHom A).comp ρ) _).trans
        (congrArg List.prod (List.map_ofFn ..))
    _ = (List.ofFn (fun i => IsNilpotent.exp (j (X i)))).prod := by
      congr 1
      apply congrArg List.ofFn
      funext i
      rw [hom_exp_eq_algebraExpUnit hExp ρ j.toLinearMap.toContinuousLinearMap hd,
        coe_algebraExpUnit]
      exact analytic_exp_eq_nilpotent_exp (hn i)
    _ = IsNilpotent.exp
        (finiteDynkinPolynomial (universalDynkinCoefficients c n) (fun i => j (X i))) :=
      bounded_associative_bch _ hw
    _ = (ρ (Exp (finiteDynkinPolynomial (universalDynkinCoefficients c n) X)) : A) := by
      rw [hom_exp_eq_algebraExpUnit hExp ρ j.toLinearMap.toContinuousLinearMap hd,
        coe_algebraExpUnit]
      change _ = NormedSpace.exp (j (finiteDynkinPolynomial _ X))
      rw [finiteDynkinPolynomial_map, analytic_exp_eq_nilpotent_exp hnp]

end PolycyclicRecognition

end

end OAI
