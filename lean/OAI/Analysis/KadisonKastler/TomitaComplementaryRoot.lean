import OAI.Analysis.KadisonKastler.TomitaRootDomain
import OAI.Analysis.KadisonKastler.TomitaResolventDenseRange
import OAI.Analysis.KadisonKastler.ConjugationFunctionalCalculus

namespace OAI

/-! # The complementary graph square root

Polar conjugation interchanges both bounded positive square roots. This
expresses the full Tomita graph using its two positive coordinates.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem conjugationOperator_nonneg (C : H ≃ₗᵢ⋆[ℂ] H)
    (hC : Function.Involutive C) {A : H →L[ℂ] H} (hA : 0 ≤ A) :
    0 ≤ conjugationOperator C A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  rw [hB, conjugationOperator_mul C hC, conjugationOperator_star C hC]
  exact star_mul_self_nonneg _

variable {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def tomitaGraphComplementRoot : H →L[ℂ] H :=
  CFC.sqrt (1 - graphResolvent M J Ω 1)

theorem tomitaGraphRoot_conjugation :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      (tomitaGraphRoot (M := M) J Ω) = tomitaGraphComplementRoot (M := M) J Ω := by
  apply Eq.symm
  apply CFC.sqrt_unique
  · rw [← conjugationOperator_mul _ (tomitaPolarConjugation_involutive J Ω hsep hcyc),
      tomitaGraphRoot_square, tomitaPolarConjugation_resolvent]
  · exact conjugationOperator_nonneg _ (tomitaPolarConjugation_involutive J Ω hsep hcyc)
      (CFC.sqrt_nonneg _)

theorem tomitaGraphComplementRoot_nonneg : 0 ≤ tomitaGraphComplementRoot (M := M) J Ω :=
  CFC.sqrt_nonneg _

include hsep hcyc in
theorem tomitaGraphComplementRoot_square :
    tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω =
      1 - graphResolvent M J Ω 1 := by
  rw [← tomitaGraphRoot_conjugation J Ω hsep hcyc,
    ← conjugationOperator_mul _ (tomitaPolarConjugation_involutive J Ω hsep hcyc),
    tomitaGraphRoot_square, tomitaPolarConjugation_resolvent]

theorem tomitaGraphRoot_polar_apply (a : H) :
    tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω a) =
      tomitaGraphComplementRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a) := by
  have h := congrArg (fun T : H →L[ℂ] H => T (tomitaPolarConjugation J Ω hsep hcyc a))
    (tomitaGraphRoot_conjugation J Ω hsep hcyc)
  change tomitaPolarConjugation J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω
    (tomitaPolarConjugation J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc a))) = _ at h
  rwa [tomitaPolarConjugation_involutive] at h

include hsep hcyc in
theorem tomitaGraphComplementRoot_injective :
    Function.Injective (tomitaGraphComplementRoot (M := M) J Ω) := by
  intro a b hab
  have h := congrArg (tomitaGraphComplementRoot (M := M) J Ω) hab
  change (tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω) a =
    (tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω) b at h
  rw [tomitaGraphComplementRoot_square J Ω hsep hcyc] at h
  exact one_sub_graphResolvent_injective J Ω hsep h

end

end KadisonKastler

end OAI
