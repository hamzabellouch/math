import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFolnerVolume
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceMetricFolner
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FolnerRatio
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! # Actual metric Følner transfer to a coarsely equivalent measured group -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Metric MeasureTheory Filter Set
open scoped Topology ENNReal

variable {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
  [DecidableEq X] [Group Y] [MetricSpace Y] [ProperSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableMul Y] [IsIsometricSMul Y Y]

theorem exists_metricFolner_sequence
    (M : InvariantMean X) (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (μ : Measure Y) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (u : X → Y) {c K C : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    ∃ A : ℕ → Set Y,
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, μ (A n) ≠ 0) ∧ (∀ n, μ (A n) ≠ ∞) ∧
      ∀ R : ℝ, 0 ≤ R → Tendsto (fun n => μ (cthickening R (A n)) / μ (A n))
        atTop (𝓝 1) := by
  classical
  let a := c + 1
  have ha : 0 < a := by dsimp [a]; linarith
  have hca : c < a := by dsimp [a]; linarith
  obtain ⟨E, hE, hlim⟩ := exists_sourceMetricFolner_sequence M hfinite
  obtain ⟨m, hm⟩ := exists_uniform_ball_multiplicity (r := a + a) u hfinite hK hlower
  let m' := m + 1
  have hmpos : 0 < (m' : ℝ) := by dsimp [m']; positivity
  have hm' : ∀ (y : Y) (F : Finset X),
      (∀ x ∈ F, dist (u x) y ≤ a + a) → F.card ≤ m' :=
    fun y F hF => (hm y F hF).trans (Nat.le_succ m)
  let A := fun n => metricFolnerSet u (E n) a
  have hAfin (n : ℕ) : μ (A n) ≠ ∞ := by
    exact measure_biUnion_ne_top (E n).finite_toSet (fun _ _ => measure_ball_ne_top)
  have hApos (n : ℕ) : 0 < μ (A n) := by
    obtain ⟨p, hp⟩ := hE n
    exact (measure_ball_pos μ (u p) ha).trans_le (measure_mono (by
      intro y hy
      exact Set.mem_iUnion₂.mpr ⟨p, hp, hy⟩))
  have hameas (n : ℕ) : MeasurableSet (A n) := metricFolnerSet_measurable u (E n) a
  let b := μ.real (ball (1 : Y) a)
  have hbpos : 0 < b :=
    ENNReal.toReal_pos (measure_ball_pos μ 1 ha).ne' measure_ball_ne_top
  have hlowerA (n : ℕ) : (b / m') * (E n).card ≤ μ.real (A n) := by
    have hv := metricFolnerSet_volume_lower μ u (E n) ha m' hm'
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (hAfin n)) hv
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmpos).mpr
    simpa only [b, Measure.real, mul_comm] using hr
  refine ⟨A, hameas, fun n => (hApos n).ne', hAfin, fun R hR => ?_⟩
  let S := K * (c + (R + 1) + a) + C
  let B := fun n => finiteMetricNeighborhood hfinite (E n) S \ E n
  let β := μ.real (closedBall (1 : Y) c)
  have hbound (n : ℕ) : μ (cthickening R (A n) \ A n) ≤
      ((B n).card : ℝ≥0∞) * μ (closedBall (1 : Y) c) :=
    metricFolnerSet_boundary_volume μ hfinite u (E n) hca hK hR hsurj hlower
  have hbdFin (n : ℕ) : μ (cthickening R (A n) \ A n) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne) (hbound n)
  have hsplit (n : ℕ) : μ (cthickening R (A n)) =
      μ (cthickening R (A n) \ A n) + μ (A n) := by
    have h := measure_sdiff_add_inter (μ := μ) (cthickening R (A n)) (hameas n)
    rw [Set.inter_eq_right.mpr (self_subset_cthickening (A n))] at h
    exact h.symm
  have hNfin (n : ℕ) : μ (cthickening R (A n)) ≠ ∞ := by
    rw [hsplit n]
    exact ENNReal.add_ne_top.mpr ⟨hbdFin n, hAfin n⟩
  have hupper (n : ℕ) : μ.real (cthickening R (A n)) ≤
      μ.real (A n) + β * (B n).card := by
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne) (hbound n)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hr
    change (μ (cthickening R (A n))).toReal ≤ _
    rw [hsplit n, ENNReal.toReal_add (hbdFin n) (hAfin n)]
    dsimp only [Measure.real, β]
    linarith
  have hreal : Tendsto (fun n => μ.real (cthickening R (A n)) / μ.real (A n))
      atTop (𝓝 1) := by
    apply tendsto_ratio_one_of_boundary _ _ (fun n => ((E n).card : ℝ))
      (fun n => ((B n).card : ℝ)) (div_pos hbpos hmpos) ENNReal.toReal_nonneg
      (fun n => by exact_mod_cast (hE n).card_pos) (fun _ => Nat.cast_nonneg _)
      hlowerA _ hupper (hlim S)
    intro n
    exact measureReal_mono (self_subset_cthickening (A n)) (hNfin n)
  have heq (n : ℕ) : ENNReal.ofReal (μ.real (cthickening R (A n)) / μ.real (A n)) =
      μ (cthickening R (A n)) / μ (A n) := by
    change ENNReal.ofReal ((μ (cthickening R (A n))).toReal / (μ (A n)).toReal) = _
    rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (hApos n).ne' (hAfin n))]
    rw [ENNReal.ofReal_toReal (hNfin n), ENNReal.ofReal_toReal (hAfin n)]
  simpa only [Function.comp_def, heq, ENNReal.ofReal_one] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal

end PolycyclicRecognition

end

end OAI
