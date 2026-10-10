import OAI.Analysis.CircleDomains.Selection.StaircaseWedge
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

/-!
# Independent uniform grid shifts

The shifts have normalized interval distribution. Any two distinct labels
have product law, so the two-shift integral equals their expected wedge cost.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def shiftLaw (h : ℝ) : Measure ℝ := ProbabilityTheory.cond volume (Icc 0 h)

theorem shiftLaw_eq (h : ℝ) :
    shiftLaw h = (ENNReal.ofReal h)⁻¹ • volume.restrict (Icc 0 h) := by
  simp only [shiftLaw, ProbabilityTheory.cond, Real.volume_Icc, sub_zero]

theorem shiftLaw_isProbabilityMeasure {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (shiftLaw h) := by
  apply cond_isProbabilityMeasure_of_finite
  · simp [Real.volume_Icc, hh]
  · simp [Real.volume_Icc]

theorem integral_shiftLaw_pair (h : ℝ) (f : ℝ × ℝ → ℝ) :
    (∫ z, f z ∂(shiftLaw h).prod (shiftLaw h)) =
      (∫ z in Icc 0 h ×ˢ Icc 0 h, f z ∂volume.prod volume) / h ^ 2 := by
  rw [shiftLaw_eq, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, ← Measure.prod_restrict, integral_smul_measure]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, smul_eq_mul]
  by_cases hh : 0 ≤ h
  · rw [ENNReal.toReal_ofReal hh]
    ring
  · have he : Icc 0 h = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hh)
    simp [he]

theorem measurePreserving_grid_pair (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    MeasurePreserving (fun θ : Fin n → ℝ => (θ i, θ j))
      (Measure.pi (fun _ => μ)) (μ.prod μ) := by
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  have hind := (iIndepFun_pi (μ := fun _ : Fin n => μ)
    (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [(measurePreserving_eval (fun _ : Fin n => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq] using hmap

theorem integral_grid_pair (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) (f : ℝ × ℝ → ℝ)
    (hf : AEStronglyMeasurable f (μ.prod μ)) :
    (∫ θ, f (θ i, θ j) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, f z ∂μ.prod μ := by
  have hp := measurePreserving_grid_pair μ hij
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ hf)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
