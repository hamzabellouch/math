import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedDoubleArity
import OAI.NumberTheory.CubicMoment.Estimates.RestrictedPrimeTuples

namespace OAI

/-! The original large rows as two independent finite prime tuples.
Both stopping-region and total-product restrictions remain literal. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def distinguishedPrimeTupleLow (i j : ℕ) (ℓ : ℤ) (ξ : ℝ)
    (Ct : ℕ) (H X : ℝ) : ℂ :=
  ((i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹)*
    ∑ f ∈ Fintype.piFinset (fun _ : Fin i =>
        primeCutoff (Real.exp primeProductWeights.radius*X)),
      ∑ g ∈ Fintype.piFinset (fun _ : Fin j =>
          primeCutoff (Real.exp primeProductWeights.radius*X)),
        if (∏ a, f a) ∈ (centralPrimaryFactors X).filter
            (fun r => ¬norm r < X^(38/100:ℝ)) then
          if (∏ b, g b) ∈ primaryProductSlice (centralProductEnvelope X)
              (Real.exp primeProductWeights.radius*X) (∏ a, f a) then
            (∏ a, distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) (f a))*
              (∏ b, (1-(primeDetectorCutoff (norm (g b)/(X^ξ)):ℂ)))*
              centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct)
                X X ((∏ a, f a)*(∏ b, g b))
          else 0
        else 0

theorem distinguishedDoubleArityLow_eq_prime_tuples
    (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) :
    distinguishedDoubleArityLow i j ℓ ξ Ct H X =
      distinguishedPrimeTupleLow i j ℓ ξ Ct H X := by
  let S := fun _ : Fin i => primeCutoff (Real.exp primeProductWeights.radius*X)
  let T := fun _ : Fin j => primeCutoff (Real.exp primeProductWeights.radius*X)
  let v := fun _ : Fin i => distinguishedPrimeWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let w := fun _ : Fin j => fun p => 1-(primeDetectorCutoff (norm p/(X^ξ)):ℂ)
  let R := (centralPrimaryFactors X).filter (fun r => ¬norm r < X^(38/100:ℝ))
  let U := primaryProductSlice (centralProductEnvelope X) (Real.exp primeProductWeights.radius*X)
  let K := fun r u => centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)
  let c := (i.factorial:ℂ)⁻¹
  let d := (j.factorial:ℂ)⁻¹
  have he : distinguishedDoubleArityLow i j ℓ ξ Ct H X =
      (c*d)*∑ r ∈ R, orderedConvolution S v r*
        ∑ u ∈ U r, orderedConvolution T w u*K r u := by
    unfold distinguishedDoubleArityLow distinguishedTupleCoefficient roughTupleCoefficient
    simp only [Fintype.card_fin,one_mul]
    change (∑ r ∈ R, (c*orderedConvolution S v r)*
      ∑ u ∈ U r, (d*orderedConvolution T w u)*K r u) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    have hu : (∑ u ∈ U r, (d*orderedConvolution T w u)*K r u) =
        d*∑ u ∈ U r, orderedConvolution T w u*K r u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring
    rw [hu]
    ring
  rw [he,orderedConvolution_double_restrict]
  rfl

end CubicFirstMoment

end

end OAI
