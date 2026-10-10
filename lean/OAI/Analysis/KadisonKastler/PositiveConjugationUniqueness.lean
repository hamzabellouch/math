import OAI.Analysis.KadisonKastler.PositivePolarUnitary
import OAI.Analysis.KadisonKastler.PolarConjugationComparison
import OAI.Analysis.KadisonKastler.CanonicalPositiveCone

namespace OAI

/-! # A positive standard conjugation is the constructed polar conjugation

The comparison unitary normalizes the algebra and fixes the reference.
Positivity of its core pairing determines it via the bounded middle
operator. No state homogeneity or uniqueness of standard forms is assumed.
-/

namespace KadisonKastler

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem tomitaPolarConjugation_eq_of_quadratic_positive
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (Ω : H) (hΩ : J Ω=Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℂ Ω (modularQuadratic J a Ω)) :
    tomitaPolarConjugation J Ω hsep hcyc=J := by
  let K := tomitaPolarConjugation J Ω hsep hcyc
  have hK : Function.Involutive K := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have hKΩ : K Ω=Ω := tomitaPolarConjugation_fixes_vector J Ω hsep hcyc
  have hKr (a : Algebra M) : conjugationOperator K a.val ∈ M.commutant :=
    tomitaPolarConjugation_right_mem J Ω hsep hcyc a
  have hKl (a : Algebra M.commutant) : conjugationOperator K a.val ∈ M := by
    have ha : a.val ∈ (conjugateRightAlgebra K hK M : Set (H →L[ℂ] H)) := by
      rw [tomitaPolarConjugation_commutant_eq J Ω hsep hcyc]
      exact a.property
    obtain ⟨b,hb,hba⟩ := ha
    rw [← hba,conjugationOperator_twice K hK]
    exact hb
  let u := conjugationPairUnitary J K
  have hu : Conjugates u M M :=
    conjugationPairUnitary_normalizes J K hJ hK hleft hright hKl hKr
  have hfix : (u : H →L[ℂ] H) Ω=Ω := conjugationPairUnitary_fixes J K Ω hΩ hKΩ
  have hcore (a : Algebra M) : 0 ≤ inner ℂ (a.val Ω)
      ((u : H →L[ℂ] H) (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω))) := by
    change 0 ≤ inner ℂ (a.val Ω) (J (K (K (star a.val Ω))))
    rw [hK]
    have hp := hpos (star a)
    change 0 ≤ inner ℂ Ω (star a.val (J (star a.val (J Ω)))) at hp
    rw [hΩ] at hp
    rw [← a.val.adjoint_inner_right]
    exact hp
  have he := positive_polar_unitary_eq_one J Ω hsep hcyc u hu hfix hcore
  apply LinearIsometryEquiv.ext
  intro x
  have hx := congrArg (fun U : H →L[ℂ] H => U x) he
  change J (K x)=x at hx
  have hh := congrArg J hx
  rw [hJ] at hh
  exact hh

end

end KadisonKastler

end OAI
