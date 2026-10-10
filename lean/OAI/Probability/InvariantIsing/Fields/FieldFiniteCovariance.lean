import OAI.Probability.InvariantIsing.Fields.FieldFiniteShiftData

namespace OAI

/-! Coordinate form of the covariance derivative of a finite-height tilted
average. This is an identity of continuous linear maps. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma fieldFiniteLinear_sub {n : ℕ} (A B : Fin n → ℝ) (a b : ℝ) :
    fieldFiniteLinear A a - fieldFiniteLinear B b =
      fieldFiniteLinear (fun i => A i - B i) (a - b) := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [sub_apply, fieldFiniteLinear_apply, sub_mul, Finset.sum_sub_distrib]
  ring

lemma field_finite_covariance {n : ℕ} (ν : Measure ℝ) (ζ : ℝ)
    (α : ℝ → ℝ) (A L : Fin n → ℝ → ℝ) (B M : ℝ → ℝ)
    (hA : ∀ i, Integrable (A i) ν) (hB : Integrable B ν)
    (hL : ∀ i, Integrable (L i) ν) (hM : Integrable M ν)
    (hαL : ∀ i, Integrable (fun u => α u * L i u) ν)
    (hαM : Integrable (fun u => α u * M u) ν) :
    (∫ u, fieldFiniteLinear (fun i => A i u) (B u) +
        (ζ * α u) • fieldFiniteLinear (fun i => L i u) (M u) ∂ν) -
      (∫ u, α u ∂ν) • (∫ u, ζ • fieldFiniteLinear (fun i => L i u) (M u) ∂ν) =
    fieldFiniteLinear
      (fun i => (∫ u, A i u ∂ν) + ζ * ((∫ u, α u * L i u ∂ν) -
        (∫ u, α u ∂ν) * (∫ u, L i u ∂ν)))
      ((∫ u, B u ∂ν) + ζ * ((∫ u, α u * M u ∂ν) -
        (∫ u, α u ∂ν) * (∫ u, M u ∂ν))) := by
  have he :
      (fun u => fieldFiniteLinear (fun i => A i u) (B u) +
        (ζ * α u) • fieldFiniteLinear (fun i => L i u) (M u)) =
      fun u => fieldFiniteLinear (fun i => A i u + ζ * (α u * L i u))
        (B u + ζ * (α u * M u)) := by
    funext u
    rw [fieldFiniteLinear_smul, fieldFiniteLinear_add]
    congr 1
    · funext i
      ring
    · ring
  have hiA (i : Fin n) : Integrable (fun u => A i u + ζ * (α u * L i u)) ν :=
    (hA i).add ((hαL i).const_mul ζ)
  have hiB : Integrable (fun u => B u + ζ * (α u * M u)) ν :=
    hB.add (hαM.const_mul ζ)
  rw [he, integral_fieldFiniteLinear ν hiA hiB, integral_smul,
    integral_fieldFiniteLinear ν hL hM, fieldFiniteLinear_smul, fieldFiniteLinear_smul,
    fieldFiniteLinear_sub]
  congr 1
  · funext i
    rw [integral_add (hA i) ((hαL i).const_mul ζ), integral_const_mul]
    ring
  · rw [integral_add hB (hαM.const_mul ζ), integral_const_mul]
    ring

end InvariantIsing

end

end OAI
