import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDrift

namespace OAI

/-! During each closed stage the locally finite prescribed drift is the
single finite array for that stage. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder

 theorem expandingDrift_eq_stage (M : Alternating.Machine)
    (hM : M.WellFormed) (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (n : ℕ) {t : ℝ} (ht : stageStart ν D K n ≤ t)
    (ht' : t ≤ stageStart ν D K (n + 1)) (x : Plane) :
    expandingDrift M hM blank m ν D K t x = stageDrift M hM blank m ν D K n t x := by
  apply tsum_eq_single n
  intro j hj
  by_cases hjn : j < n
  · apply stageDrift_zero_after M hM blank m hν hD hK
    exact ((stageStart_strictMono hν hD hK).monotone (by omega : j + 1 ≤ n)).trans ht
  · apply stageDrift_zero_before M hM blank m hν hD hK
    exact ht'.trans ((stageStart_strictMono hν hD hK).monotone (by omega : n + 1 ≤ j))

theorem expandingDrift_rigid (M : Alternating.Machine)
    (hM : M.WellFormed) (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (n : ℕ) (w : StageWire M hM blank (m + n)) {t : ℝ}
    (ht : stageStart ν D K n ≤ t) (ht' : t ≤ stageStart ν D K (n + 1))
    (x : Plane) (hx : ∀ j, |x j - wireCurve M hM blank (m + n)
      (stageStart ν D K n) (duration ν D K n) (radius ν D K n)
      (radius ν D K (n + 1)) w t j| < 2 * radius ν D K n) :
    expandingDrift M hM blank m ν D K t x =
      deriv (wireCurve M hM blank (m + n) (stageStart ν D K n)
        (duration ν D K n) (radius ν D K n) (radius ν D K (n + 1)) w) t := by
  rw [expandingDrift_eq_stage M hM blank m hν hD hK n ht ht']
  apply recorderStageField_rigid M hM blank (m + n) _
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hν hD hK n))
    (radius_pos hν hD hK n) _ w t x hx
  have hr := radius_grows hν hD hK n
  have hp := radius_pos hν hD hK n
  linarith

end ForcedComputation.ExpandingDetector

end

end OAI
