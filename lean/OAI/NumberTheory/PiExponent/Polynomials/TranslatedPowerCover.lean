import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout
import OAI.NumberTheory.PiExponent.Polynomials.PowerCoverBasis

namespace OAI

namespace PiExponent.TranslatedPowerCover

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

def Ring (_weights : σ → ℕ) (_center : σ → k) := MvPolynomial σ k

instance (w : σ → ℕ) (a : σ → k) : CommRing (Ring w a) :=
  inferInstanceAs (CommRing (MvPolynomial σ k))

def toPolynomial (w : σ → ℕ) (a : σ → k) : Ring w a ≃+* MvPolynomial σ k :=
  RingEquiv.refl _

instance (w : σ → ℕ) (a : σ → k) : Algebra (MvPolynomial σ k) (Ring w a) :=
  ((toPolynomial w a).symm.toRingHom.comp
    (translatedPowerSubstitution w a).toRingHom).toAlgebra

def decomposition (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Ring w a ≃ₗ[MvPolynomial σ k] ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  (((toPolynomial w a).toAddEquiv.trans (PowerCover.decompositionAddEquiv w hw)).trans
    (Finsupp.mapRange.addEquiv (translationEquiv a).symm.toAddEquiv)).toLinearEquiv <| by
      intro p q
      have hsub : translatedPowerSubstitution w a p =
          PowerCover.powerSubstitution w (translationEquiv a p) := by
        rw [translatedPowerSubstitution_factor]
        rfl
      change (Finsupp.mapRange.addEquiv (translationEquiv a).symm.toAddEquiv)
          (PowerCover.decompositionAddEquiv w hw
            (translatedPowerSubstitution w a p * toPolynomial w a q)) = _
      rw [hsub, PowerCover.decompositionAddEquiv_power_mul]
      ext r
      simp [Finsupp.smul_apply, smul_eq_mul]

def basis (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.Basis (∀ i, Fin (w i)) (MvPolynomial σ k) (Ring w a) where
  repr := decomposition w a hw

theorem module_free (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.Free (MvPolynomial σ k) (Ring w a) :=
  Module.Free.of_basis (basis w a hw)

theorem module_finite (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.Finite (MvPolynomial σ k) (Ring w a) := by
  classical
  exact Module.Finite.of_basis (basis w a hw)

theorem finrank (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.finrank (MvPolynomial σ k) (Ring w a) = ∏ i, w i := by
  classical
  rw [Module.finrank_eq_card_basis (basis w a hw)]
  simp [Fintype.card_pi]

end
end PiExponent.TranslatedPowerCover

end OAI
