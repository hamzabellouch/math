import OAI.Probability.StrongRayleigh.ReferenceObservation
import OAI.Probability.StrongRayleigh.MarginalBase

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.ReferenceObservation

variable {I : Type u_1} {W : Type u_2} [MeasurableSpace W]
    (μ : ProbabilityMeasure (I → Bool)) (ν : ProbabilityMeasure W)
    (B : ℝ≥0 → W → ℝ)

theorem finite_signal_hasLaw (J : Finset I) :
    HasLaw (fun ω : Space I W => fun j : J => ω.1 j)
      (finiteMarginal μ J : Measure (J → Bool)) (law μ ν) := by
  have h : HasLaw (fun x : I → Bool => fun j : J => x j)
      (finiteMarginal μ J : Measure (J → Bool)) (μ : Measure (I → Bool)) :=
    ⟨(Measurable.of_eval (fun j => measurable_pi_apply j.1)).aemeasurable, rfl⟩
  exact h.comp (signal_hasLaw μ ν)

theorem finite_noise_endpoints_hasLaw (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (S : Finset I) (t : ℝ≥0) :
    HasLaw (fun ω : Space I W => fun s : S => noise B s.1 t ω)
      (Measure.pi (fun _ : S => gaussianReal 0 t)) (law μ ν) := by
  have hInd := (iIndepFun.precomp (g := fun s : S => (s : I))
    Subtype.val_injective (iid_noise μ ν)).comp
      (fun _ w => B t w) (fun _ => hBm t)
  exact iIndepFun.hasLaw_pi
    (fun s => (hB.hasLaw_eval t).comp (noise_hasLaw μ ν s)) hInd

theorem finite_signal_noise_endpoints_hasLaw
    (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (J S : Finset I) (t : ℝ≥0) :
    HasLaw (fun ω : Space I W =>
      ((fun j : J => ω.1 j), (fun s : S => noise B s.1 t ω)))
      ((finiteMarginal μ J : Measure (J → Bool)).prod
        (Measure.pi (fun _ : S => gaussianReal 0 t))) (law μ ν) := by
  have hi : IndepFun (fun ω : Space I W => fun j : J => ω.1 j)
      (fun ω => fun s : S => noise B s.1 t ω) (law μ ν) :=
    (signal_indep_noiseField μ ν).comp
      (show Measurable (fun x : I → Bool => fun j : J => x j) by fun_prop)
      (show Measurable (fun w : I → W => fun s : S => B t (w s)) by fun_prop)
  exact hi.hasLaw_prod (finite_signal_hasLaw μ ν J)
    (finite_noise_endpoints_hasLaw μ ν B hB hBm S t)

def endpointShift (J S : Finset I) (hSJ : S ⊆ J) (t : ℝ≥0)
    (p : (J → Bool) × (S → ℝ)) : (J → Bool) × (S → ℝ) :=
  (p.1, fun s => (t : ℝ) * boolReal (p.1 ⟨s.val, hSJ s.property⟩) + p.2 s)

omit [MeasurableSpace W] in
theorem measurable_endpointShift (J S : Finset I) (hSJ : S ⊆ J) (t : ℝ≥0) :
    Measurable (endpointShift J S hSJ t) := by
  unfold endpointShift
  have hb : Measurable boolReal := measurable_of_finite _
  fun_prop

theorem finite_signal_observation_endpoints_hasLaw
    (hB : IsPreBrownianReal B (ν : Measure W))
    (hBm : ∀ t, Measurable (B t)) (J S : Finset I) (hSJ : S ⊆ J) (t : ℝ≥0) :
    HasLaw (fun ω : Space I W =>
      ((fun j : J => ω.1 j), (fun s : S => observation B s.1 t ω)))
      (Measure.map (endpointShift J S hSJ t)
        ((finiteMarginal μ J : Measure (J → Bool)).prod
          (Measure.pi (fun _ : S => gaussianReal 0 t)))) (law μ ν) := by
  have hmap : HasLaw (endpointShift J S hSJ t)
      (Measure.map (endpointShift J S hSJ t)
        ((finiteMarginal μ J : Measure (J → Bool)).prod
          (Measure.pi (fun _ : S => gaussianReal 0 t))))
      ((finiteMarginal μ J : Measure (J → Bool)).prod
          (Measure.pi (fun _ : S => gaussianReal 0 t))) :=
    ⟨(measurable_endpointShift J S hSJ t).aemeasurable, rfl⟩
  exact hmap.comp (finite_signal_noise_endpoints_hasLaw μ ν B hB hBm J S t)

end Problem336AdditiveD139.ReferenceObservation

end

end OAI
