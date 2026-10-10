import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderDynamics
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingStageTimes
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneFiniteDivergence

namespace OAI

/-! The prescribed expanding-array drift is a locally finite smooth sum.
Every stage is determined from the full finite recorder table. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector MeasureTheory
open scoped ContDiff BigOperators

def stageDrift (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (ν D K : ℝ) (n : ℕ) : ℝ → Plane → Plane :=
  recorderStageField M hM blank (m + n) (stageStart ν D K n) (duration ν D K n)
    (radius ν D K n) (radius ν D K (n + 1))

def expandingDrift (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (ν D K : ℝ) (t : ℝ) (x : Plane) : Plane :=
  detectorBlockSum (fun n y => stageDrift M hM blank m ν D K n y.1 y.2) (t, x)

theorem stageDrift_smooth (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (ν D K : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (stageDrift M hM blank m ν D K n)) :=
  recorderStageField_smooth M hM blank (m + n) _ _ _ _

theorem stageDrift_zero_before (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (n : ℕ) {t : ℝ} (ht : t ≤ stageStart ν D K n) (x : Plane) :
    stageDrift M hM blank m ν D K n t x = 0 :=
  recorderStageField_zero_before M hM blank (m + n) _
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hν hD hK n)) ht x

theorem stageDrift_zero_after (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (n : ℕ) {t : ℝ} (ht : stageStart ν D K (n + 1) ≤ t) (x : Plane) :
    stageDrift M hM blank m ν D K n t x = 0 := by
  apply recorderStageField_zero_after M hM blank (m + n) _
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hν hD hK n))
  simpa only [stageStart_succ] using ht

theorem expandingDrift_smooth (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    ContDiff ℝ ∞ (Function.uncurry (expandingDrift M hM blank m ν D K)) := by
  apply detectorBlockSum_smooth
  · exact fun n => stageDrift_smooth M hM blank m ν D K n
  · intro n y hy
    exact stageDrift_zero_before M hM blank m hν hD hK n
      (hy.le.trans (stageStart_ge hν hD hK n)) y.2

theorem expandingDrift_initial (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    {t : ℝ} (ht : t ≤ 2) (x : Plane) :
    expandingDrift M hM blank m ν D K t x = 0 := by
  have hz (n : ℕ) : stageDrift M hM blank m ν D K n t x = 0 := by
    apply stageDrift_zero_before M hM blank m hν hD hK n
    have hn := stageStart_ge hν hD hK n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  simp only [expandingDrift, detectorBlockSum, hz, tsum_zero]

theorem expandingDrift_eq_prefix (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (T : ℝ) (N : ℕ) (hN : T + 1 ≤ (N : ℝ)) {t : ℝ} (ht : t ≤ T) :
    expandingDrift M hM blank m ν D K t =
      fun x => ∑ n ∈ Finset.range N, stageDrift M hM blank m ν D K n t x := by
  funext x
  apply tsum_eq_sum
  intro n hn
  have hnN : N ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
  have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have htime := stageStart_ge hν hD hK n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply stageDrift_zero_before M hM blank m hν hD hK n
  linarith

theorem stageDrift_properties (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) (t : ℝ) :
    HasCompactSupport (stageDrift M hM blank m ν D K n t) ∧
      (∀ x, PlanarHamiltonian.divergence (stageDrift M hM blank m ν D K n t) x = 0) ∧
      (∫ x, stageDrift M hM blank m ν D K n t x) = 0 :=
  recorderStageField_properties M hM blank (m + n) _ _ (radius_pos hν hD hK n) _ t

theorem expandingDrift_divergence (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (t : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (expandingDrift M hM blank m ν D K t) x = 0 := by
  rw [expandingDrift_eq_prefix M hM blank m hν hD hK t ⌈t + 1⌉₊ (Nat.le_ceil _) le_rfl]
  have hs (n : ℕ) (_ : n ∈ Finset.range ⌈t + 1⌉₊) :
      ContDiff ℝ ∞ (fun y => stageDrift M hM blank m ν D K n t y) := by
    have hi : ContDiff ℝ ∞ (fun y : Plane => (t, y)) := contDiff_const.prodMk contDiff_id
    have hh := (stageDrift_smooth M hM blank m ν D K n).comp hi
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hh
  rw [PlanarHamiltonian.divergence_finite_sum _ _ hs]
  apply Finset.sum_eq_zero
  intro n _
  exact (stageDrift_properties M hM blank m hν hD hK n t).2.1 x

end ForcedComputation.ExpandingDetector

end

end OAI
