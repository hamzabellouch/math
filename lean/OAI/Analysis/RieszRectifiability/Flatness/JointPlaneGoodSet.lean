import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess

namespace OAI

/-!
# Simultaneous approximation by two affine planes

The joint squared-distance error defines a good set close to both planes. Its
continuity gives local integrability, and an integral error bound yields a lower
mass estimate for the good set by controlling the complementary bad set.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def jointPlaneFitError {d : ℕ} (S W : AffineSubspace ℝ (Ambient d))
    (x : Ambient d) : ℝ :=
  infDist x (S : Set (Ambient d)) ^ 2 + infDist x (W : Set (Ambient d)) ^ 2

def jointPlaneGoodSet {d : ℕ} (S W : AffineSubspace ℝ (Ambient d))
    (R η : ℝ) : Set (Ambient d) :=
  ball 0 R ∩ {x | jointPlaneFitError S W x < η ^ 2}

theorem jointPlaneFitError_continuous {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) : Continuous (jointPlaneFitError S W) :=
  ((continuous_infDist_pt (S : Set (Ambient d))).pow 2).add
    ((continuous_infDist_pt (W : Set (Ambient d))).pow 2)

theorem jointPlaneFitError_integrableOn_ball {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R : ℝ) : IntegrableOn (jointPlaneFitError S W) (ball 0 R) μ :=
  (squared_infDist_integrableOn_ball μ 0 R S hS).add
    (squared_infDist_integrableOn_ball μ 0 R W hW)

theorem jointPlaneGoodSet_distance_bounds {d : ℕ}
    (S W : AffineSubspace ℝ (Ambient d)) (R η : ℝ) (hη : 0 < η)
    (x : Ambient d) (hx : x ∈ jointPlaneGoodSet S W R η) :
    x ∈ ball (0 : Ambient d) R ∧
      infDist x (S : Set (Ambient d)) < η ∧ infDist x (W : Set (Ambient d)) < η := by
  refine ⟨hx.1, ?_, ?_⟩
  · apply (sq_lt_sq₀ infDist_nonneg hη.le).mp
    exact (le_add_of_nonneg_right (sq_nonneg (infDist x (W : Set (Ambient d))))).trans_lt hx.2
  · apply (sq_lt_sq₀ infDist_nonneg hη.le).mp
    exact (le_add_of_nonneg_left (sq_nonneg (infDist x (S : Set (Ambient d))))).trans_lt hx.2

theorem jointPlaneGoodSet_mass_lower {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (S W : AffineSubspace ℝ (Ambient d))
    (hS : (S : Set (Ambient d)).Nonempty) (hW : (W : Set (Ambient d)).Nonempty)
    (R η c : ℝ) (hη : 0 < η)
    (hmass : c * R ^ n ≤ μ.real (ball (0 : Ambient d) R))
    (herr : (∫ x in ball (0 : Ambient d) R, jointPlaneFitError S W x ∂μ) ≤
      η ^ 2 * ((c / 2) * R ^ n)) :
    (c / 2) * R ^ n ≤ μ.real (jointPlaneGoodSet S W R η) := by
  let bad : Set (Ambient d) := ball 0 R ∩ {x | η ^ 2 ≤ jointPlaneFitError S W x}
  have hmeas : MeasurableSet {x | η ^ 2 ≤ jointPlaneFitError S W x} :=
    isClosed_le continuous_const (jointPlaneFitError_continuous S W) |>.measurableSet
  have hbadmeas : MeasurableSet bad := measurableSet_ball.inter hmeas
  have hf := jointPlaneFitError_integrableOn_ball μ S W hS hW R
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (f := jointPlaneFitError S W)
    (μ := μ.restrict (ball (0 : Ambient d) R))
    (Filter.Eventually.of_forall (fun x =>
      add_nonneg (sq_nonneg (infDist x (S : Set (Ambient d))))
        (sq_nonneg (infDist x (W : Set (Ambient d)))))) hf (η ^ 2)
  rw [measureReal_restrict_apply hmeas, inter_comm] at hmarkov
  have hb : μ.real bad ≤ (c / 2) * R ^ n :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hη)).mp (hmarkov.trans herr)
  have hfinite : μ (ball (0 : Ambient d) R) ≠ ∞ :=
    ne_of_lt ((measure_mono ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Ambient d) R).measure_lt_top)
  have hset : jointPlaneGoodSet S W R η = ball (0 : Ambient d) R \ bad := by
    ext x
    simp only [jointPlaneGoodSet, bad, mem_inter_iff, mem_ofPred_eq, mem_sdiff]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, fun hb => (not_le_of_gt hlt) hb.2⟩
    · rintro ⟨hx, hout⟩
      exact ⟨hx, lt_of_not_ge (fun hle => hout ⟨hx, hle⟩)⟩
  rw [hset, measureReal_sdiff inter_subset_left hbadmeas hfinite]
  linarith

end

end RieszRectifiability

end OAI
