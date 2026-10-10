import OAI.Analysis.KadisonKastler.StateActionFubini
import OAI.Analysis.KadisonKastler.PoissonNormContinuity

namespace OAI

/-! # Bounded, norm-continuous approximations within invariant algebras -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionOrbit_zero (a : H →L[ℂ] H) : stateActionOrbit U a 0=a := by
  change unitaryConj (U 1) a=a
  rw [map_one,unitaryConj_one]

theorem stateActionOrbit_star (a : H →L[ℂ] H) (t : ℝ) :
    stateActionOrbit U (star a) t=star (stateActionOrbit U a t) := by
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))
  exact map_star e a

def poissonActionApprox (a : H →L[ℂ] H) (r : ℝ) : H →L[ℂ] H :=
  poissonVectorAverage (stateActionOrbit U a) (stateActionOrbit_continuous U hU a)
    ‖a‖ (fun t => (stateActionOrbit_norm U a t).le) 0 r

theorem poissonActionApprox_norm (a : H →L[ℂ] H) (r : ℝ) :
    ‖poissonActionApprox U hU a r‖ ≤ ‖a‖ :=
  norm_probabilityOperatorIntegral_le (ProbabilityTheory.cauchyMeasure 0 1)
    (fun t => stateActionOrbit U a (0+r*t))
    (fun x => ((stateActionOrbit_continuous U hU a x).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (norm_nonneg a)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U a (0+r*t)).le)

theorem poissonActionApprox_mem (M : VonNeumannAlgebra H)
    (hnormal : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (a : H →L[ℂ] H) (ha : a ∈ M) (r : ℝ) : poissonActionApprox U hU a r ∈ M :=
  probabilityOperatorIntegral_mem (ProbabilityTheory.cauchyMeasure 0 1)
    (fun t => stateActionOrbit U a (0+r*t))
    (fun x => ((stateActionOrbit_continuous U hU a x).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a (0+r*t)).le) M
    (Eventually.of_forall fun t => hnormal (0+r*t) a ha)

theorem poissonActionApprox_tendsto (a : H →L[ℂ] H) (x : H) :
    Tendsto (fun r => poissonActionApprox U hU a r x) (𝓝 0) (𝓝 (a x)) := by
  have h := poissonVectorAverage_tendsto (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) ‖a‖
    (fun t => (stateActionOrbit_norm U a t).le) 0 x
  simpa only [poissonActionApprox,stateActionOrbit_zero] using h

theorem poissonActionApprox_star_tendsto (a : H →L[ℂ] H) (x : H) :
    Tendsto (fun r => star (poissonActionApprox U hU a r) x) (𝓝 0) (𝓝 (star a x)) := by
  have hc (y : H) : Continuous (fun t => star (stateActionOrbit U a t) y) := by
    simp_rw [← stateActionOrbit_star]
    exact stateActionOrbit_continuous U hU (star a) y
  have h := poissonVectorAverage_star_tendsto (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) hc ‖a‖
    (fun t => (stateActionOrbit_norm U a t).le) 0 x
  simpa only [poissonActionApprox,stateActionOrbit_zero] using h

theorem poissonActionApprox_orbit_continuous (a : H →L[ℂ] H) {r : ℝ} (hr : 0 < r) :
    Continuous (stateActionOrbit U (poissonActionApprox U hU a r)) := by
  have he (s : ℝ) : stateActionOrbit U (poissonActionApprox U hU a r) s =
      poissonVectorAverage (stateActionOrbit U a) (stateActionOrbit_continuous U hU a)
        ‖a‖ (fun t => (stateActionOrbit_norm U a t).le) s r := by
    ext x
    let u := U (Multiplicative.ofAdd s)
    have hi := integrable_bounded_operator_vector (ProbabilityTheory.cauchyMeasure 0 1)
      (fun t => stateActionOrbit U a (0+r*t))
      (fun y => ((stateActionOrbit_continuous U hU a y).comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (Eventually.of_forall fun t => (stateActionOrbit_norm U a (0+r*t)).le)
      (star (u : H →L[ℂ] H) x)
    change (u : H →L[ℂ] H)
        (∫ t, stateActionOrbit U a (0+r*t) (star (u : H →L[ℂ] H) x)
          ∂ProbabilityTheory.cauchyMeasure 0 1) =
      ∫ t, stateActionOrbit U a (s+r*t) x ∂ProbabilityTheory.cauchyMeasure 0 1
    rw [← (u : H →L[ℂ] H).integral_comp_comm hi]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    change (u : H →L[ℂ] H) (stateActionOrbit U a (0+r*t) (star (u : H →L[ℂ] H) x))=
      stateActionOrbit U a (s+r*t) x
    rw [zero_add,stateActionOrbit_add]
    rfl
  change Continuous (fun s : ℝ => stateActionOrbit U (poissonActionApprox U hU a r) s)
  simp_rw [he]
  exact continuous_poissonVectorAverage (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) (norm_nonneg a)
    (fun t => (stateActionOrbit_norm U a t).le) hr

end

end KadisonKastler

end OAI
