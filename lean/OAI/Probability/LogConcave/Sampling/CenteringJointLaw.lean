import Mathlib
import OAI.Probability.LogConcave.Analysis.CenteringPotential

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

lemma centering_joint_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    (gibbs (centeringPotential F x r T)).map (productPointEquiv d d)=
      (interpolationLaw F x r T).prod (stdGaussian (Point d)) := by
  rw [interpolationLaw_eq_gibbs hF x hr (by linarith) (by nlinarith)]
  exact (productPotential_gibbs
    (interpolationPotential_smooth hF x hr hl hT0 hT1).continuous
      (gaussianPotential_polySmooth d).smooth.continuous).trans
    (by rw [gaussianPotential_gibbs])

lemma centering_position_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    (gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d y).1)=
      interpolationLaw F x r T := by
  change (gibbs (centeringPotential F x r T)).map (Prod.fst ∘ (productPointEquiv d d))=_
  rw [←Measure.map_map measurable_fst (productPointEquiv d d).continuous.measurable,
    centering_joint_law hF x hr hl hT0 hT1]
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

lemma harmonic_position_law {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    {Ψ : Point (d+d) → Point (d+d)} (hm : Measurable Ψ)
    (hlaw : (gibbs (centeringPotential F x r T)).map Ψ=gibbs (centeringPotential F x r T)) :
    (gibbs (centeringPotential F x r T)).map (fun y => (productPointEquiv d d (Ψ y)).1)=
      interpolationLaw F x r T := by
  change (gibbs (centeringPotential F x r T)).map ((fun y => (productPointEquiv d d y).1) ∘ Ψ)=_
  rw [←Measure.map_map ((productPointEquiv d d).continuous.measurable.fst) hm,hlaw]
  exact centering_position_law hF x hr hl hT0 hT1

lemma rms_bound_pullback {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure X} {ν : Measure Y} {f : X → Y} (hf : Measurable f) (hlaw : μ.map f=ν)
    {e : Y → E} (he : Measurable e) (hi : Integrable (fun y => ‖e y‖^2) ν)
    {B : ℝ} (hB : (∫y,‖e y‖^2 ∂ν)≤B) :
    Integrable (fun x => ‖e (f x)‖^2) μ ∧ (∫x,‖e (f x)‖^2 ∂μ)≤B := by
  rw [←hlaw] at hi
  refine ⟨hi.comp_measurable hf,?_⟩
  rw [←integral_map hf.aemeasurable (he.norm.pow_const 2).aestronglyMeasurable,hlaw]
  exact hB

end LogConcaveSampling

end

end

end

end OAI
