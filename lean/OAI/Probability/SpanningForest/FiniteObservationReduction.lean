import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace Problem336.GaussianObservation

variable {I : Type*}

def bitValue (b : Bool) : ℝ := if b then 1 else 0

theorem bitValue_binary (b : Bool) : bitValue b = 0 ∨ bitValue b = 1 := by
  cases b <;> simp [bitValue]

theorem finiteProjection_integrable (ν : Measure (I → Bool)) [IsFiniteMeasure ν]
    (A : Finset I) (F : (A → Bool) → ℝ) :
    Integrable (fun ω => F (A.restrict ω)) ν := by
  exact (Integrable.of_finite (μ := ν.map A.restrict) (f := F)).comp_measurable
    (Finset.measurable_restrict A)

theorem finiteProjection_integral (ν : Measure (I → Bool)) [IsFiniteMeasure ν]
    (A : Finset I) (F : (A → Bool) → ℝ) :
    (∫ ω, F (A.restrict ω) ∂ν) =
      ∑ a : A → Bool, (ν.map A.restrict).real {a} * F a := by
  have hF : Integrable F (ν.map A.restrict) := Integrable.of_finite
  have hA : HasLaw A.restrict (ν.map A.restrict) ν :=
    ⟨(Finset.measurable_restrict A).aemeasurable, rfl⟩
  calc
    _ = ∫ a, F a ∂ν.map A.restrict := hA.integral_comp hF.aestronglyMeasurable
    _ = _ := by simpa only [smul_eq_mul] using integral_fintype hF

theorem finiteProjection_mass_sum (ν : Measure (I → Bool)) [IsProbabilityMeasure ν]
    (A : Finset I) :
    (∑ a : A → Bool, (ν.map A.restrict).real {a}) = 1 := by
  simp

def finiteTiltMean (ν : Measure (I → Bool)) (S : Finset I)
    (h : I → ℝ) (e : I) : ℝ :=
  (∫ ω, bitValue (ω e) * Real.exp (∑ j : S, h j * bitValue (ω j)) ∂ν) /
    (∫ ω, Real.exp (∑ j : S, h j * bitValue (ω j)) ∂ν)

theorem integrable_finiteTiltWeight (ν : Measure (I → Bool)) [IsFiniteMeasure ν]
    (S : Finset I) (h : I → ℝ) :
    Integrable (fun ω => Real.exp (∑ j : S, h j * bitValue (ω j))) ν :=
  finiteProjection_integrable ν S (fun a => Real.exp (∑ j : S, h j * bitValue (a j)))

theorem finiteTilt_denominator_pos (ν : Measure (I → Bool)) [IsProbabilityMeasure ν]
    (S : Finset I) (h : I → ℝ) :
    0 < ∫ ω, Real.exp (∑ j : S, h j * bitValue (ω j)) ∂ν :=
  integral_exp_pos (integrable_finiteTiltWeight ν S h)

theorem finiteTiltMean_eq_marginal_sum (ν : Measure (I → Bool)) [IsFiniteMeasure ν]
    (S A : Finset I) (hSA : S ⊆ A) (h : I → ℝ) (e : I) (he : e ∈ A) :
    finiteTiltMean ν S h e =
      (∑ a : A → Bool, (ν.map A.restrict).real {a} *
        (bitValue (a ⟨e, he⟩) *
          Real.exp (∑ j : S, h j * bitValue (a ⟨j, hSA j.property⟩)))) /
      (∑ a : A → Bool, (ν.map A.restrict).real {a} *
        Real.exp (∑ j : S, h j * bitValue (a ⟨j, hSA j.property⟩))) := by
  unfold finiteTiltMean
  rw [← finiteProjection_integral ν A
    (fun a => bitValue (a ⟨e, he⟩) *
      Real.exp (∑ j : S, h j * bitValue (a ⟨j, hSA j.property⟩))),
    ← finiteProjection_integral ν A
      (fun a => Real.exp (∑ j : S, h j * bitValue (a ⟨j, hSA j.property⟩)))]
  rfl

end Problem336.GaussianObservation

end

end OAI
