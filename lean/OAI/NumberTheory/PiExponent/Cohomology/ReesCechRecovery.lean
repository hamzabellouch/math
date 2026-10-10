import OAI.NumberTheory.PiExponent.Cohomology.GradedSerreVanishing
import OAI.NumberTheory.PiExponent.Cohomology.ReesCechInjectivity

namespace OAI

namespace PiExponent.ReesCechRecovery
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {R J : Type u} [CommRing R] [IsNoetherianRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem eventually_ordinary_power_recovery
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ q : ℕ, GradedSerreStep.HasPrimitive (J := J) (R := R) (integerPiece I) n q) ∧
      (∀ c : Cochain (grading (J := J) (R := R)) (integerPiece I)
          MvPolynomial.X variable_mem n 0,
        differential (grading (J := J) (R := R)) (integerPiece I)
          MvPolynomial.X variable_mem n c = 0 →
        ∃! z : ↥(I ^ n : Ideal R),
          augmentation (grading (J := J) (R := R)) (integerPiece I)
            MvPolynomial.X variable_mem n (ordinaryPowerEquivIntegerPiece I n z) = c) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  let : Module.Finite (MvPolynomial J R) (reesAlgebra I) := finite_presented_module I a ha
  obtain ⟨N₁, h₁⟩ := GradedSerreVanishing.eventually_all_positive (J := J) (R := R)
    (integerPiece I)
  obtain ⟨N₂, h₂⟩ := GradedSerreVanishing.eventually_augmentation_recovery (J := J) (R := R)
    (integerPiece I)
  obtain ⟨N₃, h₃⟩ := ReesCechInjectivity.eventually_augmentation_injective I a ha
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨h₁ n hn₁, ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := h₂ n hn₂ c hc
  refine ⟨(ordinaryPowerEquivIntegerPiece I n).symm m, ?_, ?_⟩
  · simpa only [AddEquiv.apply_symm_apply] using hm
  · intro z hz
    apply (ordinaryPowerEquivIntegerPiece I n).injective
    rw [AddEquiv.apply_symm_apply]
    exact h₃ n hn₃ (hz.trans hm.symm)

end
end PiExponent.ReesCechRecovery

end OAI
