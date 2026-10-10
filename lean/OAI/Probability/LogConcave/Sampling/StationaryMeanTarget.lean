import Mathlib
import OAI.Probability.LogConcave.Dynamics.StationaryPath

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T s : ℝ}
  (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0<s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

def stationaryMeanTarget (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s))) (y : Point (d+d)) : Point d :=
  s • (productPointEquiv d d y).2+
    ∫t in (0:ℝ)..1,conditionalFieldMean F x r T (productPointEquiv d d (X.path y t)).1

include hlam hs in
lemma stationaryMeanTarget_identity (y : Point (d+d)) :
    stationaryMeanTarget hF x hr hl hT0 hT1 X y=
      primitiveExpectedField F x r+s • (productPointEquiv d d (X.path y 1)).2 := by
  let E := productPointEquiv d d
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
    E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (X.derivative y t ht)
  have hd' (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      HasDerivWithinAt (fun u => E (X.path y u))
        (skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
          (fun z => conditionalFieldMean F x r T z-primitiveExpectedField F x r) s
          (E (X.path y t))) (Icc (0:ℝ) 1) t := by
    convert! hd t ht using 1
    exact (actual_centering_joint_field hF x hr hlam hl hT0 hT1 s (X.path y t)).symm
  have he := centering_momentum_identity
    (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).continuous
    (primitiveExpectedField F x r) hs (E.continuous.comp (X.continuous y)) hd'
  simpa only [stationaryMeanTarget,Function.comp_def,X.initial,E] using he

include hlam hs in

theorem stationaryMeanTarget_law :
    (gibbs (centeringPotential F x r T)).map (stationaryMeanTarget hF x hr hl hT0 hT1 X)=
      (stdGaussian (Point d)).map (fun g => primitiveExpectedField F x r+s • g) := by
  let E := productPointEquiv d d
  have hm : Measurable (fun y : Point (d+d) => primitiveExpectedField F x r+s • (E y).2) := by
    exact measurable_const.add (E.continuous.measurable.snd.const_smul s)
  have he : stationaryMeanTarget hF x hr hl hT0 hT1 X=
      (fun y : Point (d+d) => primitiveExpectedField F x r+s • (E y).2) ∘ (fun y => X.path y 1) := by
    funext y
    exact stationaryMeanTarget_identity hF x hr hlam hl hT0 hT1 hs X y
  rw [he,←Measure.map_map hm (X.measurable_slice 1),X.law 1 ⟨by norm_num,le_rfl⟩]
  change (gibbs (centeringPotential F x r T)).map (((fun g : Point d => primitiveExpectedField F x r+s • g) ∘ Prod.snd) ∘ E)=_
  rw [←Measure.map_map (by fun_prop) E.continuous.measurable,
    centering_joint_law hF x hr.le hl hT0 hT1,
    ←Measure.map_map (by fun_prop) measurable_snd,Measure.map_snd_prod]
  let : IsProbabilityMeasure (interpolationLaw F x r T) :=
    interpolationLaw_probability hF x hr.le (by linarith only [hl]) T
  rw [measure_univ,one_smul]
end LogConcaveSampling

end

end

end OAI
