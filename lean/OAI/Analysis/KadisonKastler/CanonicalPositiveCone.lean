import OAI.Analysis.KadisonKastler.ModularPositiveCone
import OAI.Analysis.KadisonKastler.TomitaPositivePairing
import OAI.Analysis.KadisonKastler.ModularOrbitCommutant

namespace OAI

/-! # Positivity of the cone for the constructed modular conjugation

The positive core pairing and the constructed commutant theorem make the
generated cone acute. In particular its intersection with its negative is
zero. Self-duality and representation of all normal states are not asserted.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
  (hsep : Function.Injective (algebraVectorMap M ξ))
  (hcyc : DenseRange (algebraVectorMap M ξ))

def canonicalModularPositiveCone : ConvexCone ℝ H :=
  modularPositiveCone (M := M) (tomitaPolarConjugation J ξ hsep hcyc) ξ

theorem tomitaPolarConjugation_right_mem (a : Algebra M) :
    conjugationOperator (tomitaPolarConjugation J ξ hsep hcyc) a.val ∈ M.commutant := by
  rw [← tomitaPolarConjugation_commutant_eq J ξ hsep hcyc]
  exact ⟨a.val,a.property,rfl⟩

theorem canonicalModularPositiveCone_acute {η ζ : H}
    (hη : η ∈ canonicalModularPositiveCone J ξ hsep hcyc)
    (hζ : ζ ∈ canonicalModularPositiveCone J ξ hsep hcyc) :
    0 ≤ (inner ℂ η ζ).re := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  change 0 ≤ inner ℝ η ζ
  apply modularPositiveCone_acute _ (tomitaPolarConjugation_involutive J ξ hsep hcyc)
    (tomitaPolarConjugation_right_mem J ξ hsep hcyc) ξ ?_ hη hζ
  intro a
  exact (tomitaPolarConjugation_quadratic_nonneg J ξ hsep hcyc a).1

theorem canonicalModularPositiveCone_eq_zero_of_neg_mem {η : H}
    (hη : η ∈ canonicalModularPositiveCone J ξ hsep hcyc)
    (hnη : -η ∈ canonicalModularPositiveCone J ξ hsep hcyc) : η = 0 := by
  have h := canonicalModularPositiveCone_acute J ξ hsep hcyc hη hnη
  rw [inner_neg_right,Complex.neg_re,← RCLike.re_eq_complex_re,
    ← norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg η])

end

end KadisonKastler

end OAI
