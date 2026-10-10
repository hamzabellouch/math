import OAI.Analysis.KadisonKastler.StateOrbitBicentralizer
import OAI.Analysis.KadisonKastler.StateOrbitMinimalCore

namespace OAI

/-! # Scalar weak orbit hulls from triviality of the bicentralizer

This constructs the implication in Haagerup, Acta Math. 158 (1987),
Proposition 1.3(2)(a) to (b). No orbit-averaging hypothesis is used.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance scalarHullsRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem scalar_stateOrbitHulls_of_stateBicentralizer
    (ξ : H) (hsep : Function.Injective (algebraVectorMap M ξ))
    (hscalar : ∀ b : Algebra M, stateBicentralizerMember ξ b → ∃ z : ℂ, b=z • 1)
    (a : Algebra M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ z : ℂ, ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
      closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) := by
  obtain ⟨b,hb,hcore⟩ := exists_singleton_stateOrbitCore ξ hsep a
  obtain ⟨z,hz⟩ := hscalar b (singleton_stateOrbitCore_stateBicentralizer ξ hsep b hcore)
  refine ⟨z,?_⟩
  rw [hz] at hb
  exact hb δ hδ

theorem scalar_stateOrbitHulls_of_bicentralizer
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hsep : Function.Injective (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (hscalar : ∀ b : Algebra M, vectorBicentralizerMember J ξ b →
      ∃ z : ℂ, b=z • 1)
    (a : Algebra M) (δ : ℝ) (hδ : 0 < δ) :
    ∃ z : ℂ, ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
      closedConvexHull ℝ (stateUnitaryOrbit ξ a δ) := by
  obtain ⟨b,hb,hcore⟩ := exists_singleton_stateOrbitCore ξ hsep a
  obtain ⟨z,hz⟩ := hscalar b
    (singleton_stateOrbitCore_bicentralizer J hJ hright hleft ξ hξ hcyc hpos b hcore)
  refine ⟨z,?_⟩
  rw [hz] at hb
  exact hb δ hδ

end

end KadisonKastler

end OAI
