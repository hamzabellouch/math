import OAI.Analysis.KadisonKastler.TomitaPolarCorePairing
import OAI.Analysis.KadisonKastler.TomitaVectorFixed
import OAI.Analysis.KadisonKastler.ModularPositiveOperator

namespace OAI

/-! # Positivity of the modular quadratic vectors

The two commuting positive graph roots give the positive core pairing
for the constructed polar conjugation. No natural-cone axiom is assumed.
-/

namespace KadisonKastler

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem tomitaPolarConjugation_positive_pairing (a : Algebra M) :
    0 ≤ inner ℂ (a.val Ω) (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω)) := by
  rw [← tomitaCoreCoordinate_first J Ω hsep hcyc a,
    ← tomitaCoreCoordinate_complement J Ω hsep hcyc a,
    ← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [hs]
  have hp : 0 ≤ tomitaGraphRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω :=
    Commute.mul_nonneg (CFC.sqrt_nonneg _) (tomitaGraphComplementRoot_nonneg J Ω)
      (tomitaGraphRoots_commute J Ω)
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).inner_nonneg_right _

theorem tomitaPolarConjugation_quadratic_nonneg (a : Algebra M) :
    0 ≤ inner ℂ Ω (a.val (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
      a.val Ω)) := by
  have he := tomitaPolarConjugation_positive_pairing J Ω hsep hcyc (star a)
  simp only [StarMemClass.coe_star,star_star] at he
  change 0 ≤ inner ℂ Ω (a.val (tomitaPolarConjugation J Ω hsep hcyc
    (a.val (tomitaPolarConjugation J Ω hsep hcyc Ω))))
  rw [tomitaPolarConjugation_fixes_vector J Ω hsep hcyc,
    ← ContinuousLinearMap.adjoint_inner_left]
  exact he

end

end KadisonKastler

end OAI
