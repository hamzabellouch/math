import OAI.Probability.SpanningForest.BinaryGaussianPosterior
import OAI.Probability.SpanningForest.PosteriorTiltLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators ProbabilityTheory

namespace Problem336.FinitePosterior

lemma gaussianFiniteTilt_finset_eq {I : Type*}
    (ν : ProbabilityMeasure (I → Bool)) (S : Finset I)
    (e : I) (t : ℝ) (y : I → ℝ) :
    gaussianFiniteTilt (ν : Measure (I → Bool)) (fun i : S => (i : I)) e t
      (fun i => y i) =
      TiltLimit.finiteTiltMean ν S (fun i => y i - t / 2) e := by
  classical
  have hsum (x : I → Bool) :
      (∑ j : S, (y j - t / 2) * binaryValue (x j)) =
        ∑ j ∈ S, (y j - t / 2) * binaryValue (x j) :=
    Finset.sum_coe_sort S (fun j => (y j - t / 2) * binaryValue (x j))
  unfold gaussianFiniteTilt TiltLimit.finiteTiltMean TiltLimit.tiltedMean TiltLimit.finiteEnergy
  simp_rw [hsum]
  simp only [binaryValue, TiltLimit.bit, mul_comm]

theorem binaryField_finset_condExp
    {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ProbabilityMeasure (I → Bool))
    (X : Ω → (I → Bool)) (noise : Ω → (I → ℝ))
    (hX : Measurable X) (hnoise : Measurable noise)
    (S : Finset I) (e : I) (t : ℝ≥0) (ht : t ≠ 0)
    (hprior : P.map X = (ν : Measure (I → Bool)))
    (hnoiseLaw : P.map (fun ω (i : S) => noise ω i) =
      Measure.pi (fun _ : S => gaussianReal 0 t))
    (hindep : X ⟂ᵢ[P] noise) :
    let Y := fun ω i => (t : ℝ) * TiltLimit.bit (X ω i) + noise ω i
    P[fun ω => TiltLimit.bit (X ω e) |
      (inferInstance : MeasurableSpace (S → ℝ)).comap (fun ω (i : S) => Y ω i)] =ᵐ[P]
      fun ω => TiltLimit.finiteTiltMean ν S (fun i => Y ω i - (t : ℝ) / 2) e := by
  classical
  let restrict : (I → ℝ) → S → ℝ := fun y i => y i
  have hr : Measurable restrict := Measurable.of_eval (fun i => measurable_pi_apply (i : I))
  have hi : X ⟂ᵢ[P] (fun ω (i : S) => noise ω i) := by
    simpa only [Function.comp_def, id_eq] using hindep.comp measurable_id hr
  have h := binaryField_gaussian_condExp P (ν : Measure (I → Bool)) X
    (fun ω (i : S) => noise ω i) hX (hr.comp hnoise)
    (fun i : S => (i : I)) e t ht hprior hnoiseLaw hi
  filter_upwards [h] with ω hω
  exact hω.trans (gaussianFiniteTilt_finset_eq ν S e t
    (fun i => (t : ℝ) * binaryValue (X ω i) + noise ω i))

end Problem336.FinitePosterior

end

end OAI
