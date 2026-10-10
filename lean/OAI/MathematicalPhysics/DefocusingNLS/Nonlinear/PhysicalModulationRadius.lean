import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalReferenceModulation

namespace OAI

/-! # Continuous physical parameters with a positive similarity radius -/

open Metric
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Params" => ProfileSymmetryParameters
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] physicalStartingPerturbation physicalStartingOperator
  sobolevTranslation

noncomputable def physicalModulationRadius (R : Radius) (p : Params) : Radius :=
  ⟨max 1 (expandingRadius R.1 (-p.2.2)), le_max_left _ _⟩

theorem continuous_physicalModulationRadius (R : Radius) :
    Continuous (physicalModulationRadius R) := by
  apply Continuous.subtype_mk
  unfold expandingRadius
  fun_prop

theorem physicalModulationRadius_bounds (R : Radius) (hR : 2 ≤ R.1)
    (p : Params) (hp : ‖p‖ ≤ 2 * Real.log 2) :
    (physicalModulationRadius R p).1 = expandingRadius R.1 (-p.2.2) ∧
      R.1 ≤ 2 * (physicalModulationRadius R p).1 ∧
      (physicalModulationRadius R p).1 ≤ 2 * R.1 := by
  have ht : |p.2.2| ≤ 2 * Real.log 2 :=
    (show |p.2.2| ≤ ‖p‖ by simpa only [Real.norm_eq_abs] using
      (norm_snd_le p.2).trans (norm_snd_le p)).trans hp
  have hlo : (1 / 2 : ℝ) ≤ Real.exp (-p.2.2 / 2) := by
    have h := Real.exp_le_exp.mpr
      (show -Real.log 2 ≤ -p.2.2 / 2 by linarith [(abs_le.mp ht).2])
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have hhi : Real.exp (-p.2.2 / 2) ≤ 2 := by
    have h := Real.exp_le_exp.mpr
      (show -p.2.2 / 2 ≤ Real.log 2 by linarith [(abs_le.mp ht).1])
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have hlow : 1 ≤ expandingRadius R.1 (-p.2.2) := by
    unfold expandingRadius
    nlinarith
  have he : (physicalModulationRadius R p).1 = expandingRadius R.1 (-p.2.2) :=
    max_eq_right hlow
  refine ⟨he, ?_, ?_⟩ <;> rw [he] <;> unfold expandingRadius <;> nlinarith

theorem physicalModulationRadius_cancel (R : Radius) (hR : 2 ≤ R.1)
    (p : Params) (hp : ‖p‖ ≤ 2 * Real.log 2) :
    R.1 = expandingRadius (physicalModulationRadius R p).1 p.2.2 := by
  rw [(physicalModulationRadius_bounds R hR p hp).1]
  unfold expandingRadius
  rw [mul_assoc, ← Real.exp_add]
  have he : -p.2.2 / 2 + p.2.2 / 2 = 0 := by ring
  rw [he, Real.exp_zero, mul_one]

theorem continuous_euclideanToTorus : Continuous euclideanToTorus := by
  apply continuous_pi
  intro i
  exact continuous_quotient_mk'.comp (by fun_prop)

theorem continuous_physicalModulation_shift (R : Radius) :
    Continuous (fun p : Params =>
      euclideanToTorus ((1 / (physicalModulationRadius R p).1) • p.2.1)) := by
  apply continuous_euclideanToTorus.comp
  have hc : Continuous (fun p : Params => 1 / (physicalModulationRadius R p).1) :=
    continuous_const.div
      (continuous_subtype_val.comp (continuous_physicalModulationRadius R))
      (fun p => ne_of_gt (lt_of_lt_of_le zero_lt_one (physicalModulationRadius R p).2))
  exact hc.smul (continuous_fst.comp continuous_snd)

theorem continuous_physicalModulation_perturbation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (R : Radius) (f : FourierL2) :
    Continuous (fun p : Params =>
      physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ
        (physicalModulationRadius R p) p.1
        (euclideanToTorus ((1 / (physicalModulationRadius R p).1) • p.2.1)) f) := by
  exact (continuous_physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ).comp
    (((continuous_physicalModulationRadius R).prodMk
      (continuous_fst.prodMk (continuous_physicalModulation_shift R))).prodMk continuous_const)

end DefocusingNLS

end OAI
