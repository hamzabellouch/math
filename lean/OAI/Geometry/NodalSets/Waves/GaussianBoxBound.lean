import Mathlib.MeasureTheory.Constructions.Pi
import OAI.Geometry.NodalSets.Waves.GaussianIntervalBound

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma gaussian_box_bound (mean center : ι → ℝ) (radius : ℝ) (hr : 0 ≤ radius)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun i ↦ gaussianReal (mean i) v))
      (Set.pi univ (fun i ↦ Icc (center i-radius) (center i+radius))) ≤
      ENNReal.ofReal ((2*radius/(Real.sqrt (2*Real.pi*v)))^(Fintype.card ι)) := by
  classical
  rw [Measure.pi_pi]
  calc
    _ ≤ ∏ i : ι, ENNReal.ofReal (2*radius/(Real.sqrt (2*Real.pi*v))) :=
      Finset.prod_le_prod (fun i _ ↦ gaussian_interval_bound (mean i) (center i) radius hr v hv)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ]
      rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 2*radius/(Real.sqrt (2*Real.pi*v)))]

lemma gaussian_coord_ball_bound (mean center : ι → ℝ) (radius : ℝ) (hr : 0 ≤ radius)
    (v : ℝ≥0) (hv : v ≠ 0) :
    (Measure.pi (fun i ↦ gaussianReal (mean i) v)) {z | ‖z-center‖ ≤ radius} ≤
      ENNReal.ofReal ((2*radius/(Real.sqrt (2*Real.pi*v)))^(Fintype.card ι)) := by
  apply le_trans (measure_mono ?_) (gaussian_box_bound mean center radius hr v hv)
  intro z hz i _
  have h := (norm_le_pi_norm (z-center) i).trans hz
  change |z i-center i| ≤ radius at h
  exact ⟨by linarith [(abs_le.mp h).1],by linarith [(abs_le.mp h).2]⟩

end
end Yau.Probability

end OAI
