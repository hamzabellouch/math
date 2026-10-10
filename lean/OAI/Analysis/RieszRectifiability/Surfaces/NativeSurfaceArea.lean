import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic

namespace OAI

/-!
# Intrinsic surface-area measures

The native surface-area measure is Hausdorff measure restricted to the surface.
Upper area growth gives local finiteness and regularity, while lower area bounds
identify the support when the surface is closed.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped ENNReal

def nativeSurfaceArea {d : ℕ} (n : ℕ) (A : Set (Ambient d)) : Measure (Ambient d) :=
  (μH[(n : ℝ)] : Measure (Ambient d)).restrict A

theorem nativeSurfaceArea_apply {n d : ℕ} (A B : Set (Ambient d))
    (hB : MeasurableSet B) :
    nativeSurfaceArea n A B = (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ B) := by
  rw [nativeSurfaceArea, Measure.restrict_apply hB, inter_comm]

theorem nativeSurfaceArea_open_ball_lower {n d : ℕ}
    (A : Set (Ambient d)) (c : ℝ≥0∞)
    (hlower : ∀ p ∈ A, ∀ r : ℝ, 0 < r →
      c * (ENNReal.ofReal r) ^ n ≤
        (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r))
    (p : Ambient d) (hp : p ∈ A) (r : ℝ) (hr : 0 < r) :
    (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n) * (ENNReal.ofReal r) ^ n ≤
      nativeSurfaceArea n A (ball p r) := by
  rw [nativeSurfaceArea_apply A _ measurableSet_ball]
  have h := hlower p hp (r / 2) (by positivity)
  have heq : c * (ENNReal.ofReal (r / 2)) ^ n =
      (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n) * (ENNReal.ofReal r) ^ n := by
    rw [show r / 2 = (1 / 2) * r by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow]
    exact (mul_assoc _ _ _).symm
  rw [heq] at h
  exact h.trans (measure_mono (inter_subset_inter_right _
    (closedBall_subset_ball (by linarith : r / 2 < r))))

theorem nativeSurfaceArea_global_upper_growth {n d : ℕ}
    (A : Set (Ambient d)) (C : ℝ≥0∞) (hC : C < ⊤)
    (hupper : ∀ (p : Ambient d) (r : ℝ), 0 < r →
      (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r) ≤
        C * (ENNReal.ofReal r) ^ n) :
    GlobalUpperGrowth n C.toReal (nativeSurfaceArea n A) := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  intro p r hr
  rw [nativeSurfaceArea_apply A _ measurableSet_ball,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne,
    ENNReal.ofReal_pow hr.le]
  exact (measure_mono (inter_subset_inter_right _ ball_subset_closedBall)).trans
    (hupper p r hr)

theorem nativeSurfaceArea_regular {n d : ℕ}
    (A : Set (Ambient d)) (C : ℝ≥0∞) (hC : C < ⊤)
    (hupper : ∀ (p : Ambient d) (r : ℝ), 0 < r →
      (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r) ≤
        C * (ENNReal.ofReal r) ^ n) :
    (nativeSurfaceArea n A).Regular := by
  have hg := nativeSurfaceArea_global_upper_growth A C hC hupper
  let : IsLocallyFiniteMeasure (nativeSurfaceArea n A) :=
    ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num),
      (hg.2 x 1 (by norm_num)).trans_lt ENNReal.ofReal_lt_top⟩⟩
  infer_instance

theorem nativeSurfaceArea_support {n d : ℕ}
    (A : Set (Ambient d)) (hA : IsClosed A) (c : ℝ≥0∞) (hc : 0 < c)
    (hlower : ∀ p ∈ A, ∀ r : ℝ, 0 < r →
      c * (ENNReal.ofReal r) ^ n ≤
        (μH[(n : ℝ)] : Measure (Ambient d)) (A ∩ closedBall p r)) :
    (nativeSurfaceArea n A).support = A := by
  apply Subset.antisymm
  · exact (nativeSurfaceArea n A).support_subset_of_isClosed hA
      (ae_restrict_mem hA.measurableSet)
  · intro p hp
    apply ((nativeSurfaceArea n A).mem_support_iff_forall p).mpr
    intro U hU
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
    have hpos : 0 < (c * (ENNReal.ofReal (1 / 2 : ℝ)) ^ n) * (ENNReal.ofReal r) ^ n := by
      positivity
    exact (hpos.trans_le (nativeSurfaceArea_open_ball_lower A c hlower p hp r hr)).trans_le
      (measure_mono hsub)

end

end RieszRectifiability

end OAI
