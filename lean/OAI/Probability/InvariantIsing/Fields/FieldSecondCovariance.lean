import OAI.Probability.InvariantIsing.Fields.FieldAffineAverageDerivative

namespace OAI

/-! The two-coordinate covariance algebra for second derivatives of
the scalar Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma field_pair_covariance (ν : Measure ℝ) (ζ : ℝ)
    (α A B L M : ℝ → ℝ)
    (hA : Integrable A ν) (hB : Integrable B ν)
    (hL : Integrable L ν) (hM : Integrable M ν)
    (hαL : Integrable (fun u => α u * L u) ν)
    (hαM : Integrable (fun u => α u * M u) ν) :
    (∫ u, pairLinear (A u) (B u) + (ζ * α u) • pairLinear (L u) (M u) ∂ν) -
        (∫ u, α u ∂ν) • (∫ u, ζ • pairLinear (L u) (M u) ∂ν) =
      pairLinear
        ((∫ u, A u ∂ν) + ζ * ((∫ u, α u * L u ∂ν) - (∫ u, α u ∂ν) * (∫ u, L u ∂ν)))
        ((∫ u, B u ∂ν) + ζ * ((∫ u, α u * M u ∂ν) - (∫ u, α u ∂ν) * (∫ u, M u ∂ν))) := by
  have he : (fun u => pairLinear (A u) (B u) + (ζ * α u) • pairLinear (L u) (M u)) =
      fun u => pairLinear (A u + ζ * (α u * L u)) (B u + ζ * (α u * M u)) := by
    funext u
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, smul_apply, pairLinear_apply, smul_eq_mul]
    ring
  have hiA : Integrable (fun u => A u + ζ * (α u * L u)) ν := hA.add (hαL.const_mul ζ)
  have hiB : Integrable (fun u => B u + ζ * (α u * M u)) ν := hB.add (hαM.const_mul ζ)
  have heA : (∫ u, A u + ζ * (α u * L u) ∂ν) =
      (∫ u, A u ∂ν) + ζ * ∫ u, α u * L u ∂ν := by
    rw [integral_add hA (hαL.const_mul ζ), integral_const_mul]
  have heB : (∫ u, B u + ζ * (α u * M u) ∂ν) =
      (∫ u, B u ∂ν) + ζ * ∫ u, α u * M u ∂ν := by
    rw [integral_add hB (hαM.const_mul ζ), integral_const_mul]
  rw [he, integral_pairLinear ν hiA hiB, heA, heB, integral_smul,
    integral_pairLinear ν hL hM]
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply, pairLinear_apply, smul_eq_mul]
  ring

end InvariantIsing

end

end OAI
