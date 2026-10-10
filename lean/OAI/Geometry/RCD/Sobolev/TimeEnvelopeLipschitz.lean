import OAI.Geometry.RCD.Heat.TimeLowerEnvelope
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # Spatial Lipschitz continuity of the monotone time envelope -/

open Set Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y]

theorem timeLowerEnvelope_lipschitz {M : ℝ} (hM : 0 ≤ M)
    (s : ℕ → ℝ) (v : ℕ → Y → ℝ) (L : ℝ≥0)
    (hv : ∀ i x, |v i x| ≤ M) (hL : ∀ i, LipschitzWith L (v i)) (t : ℝ) :
    LipschitzWith L (fun x => timeLowerEnvelope M s (fun i => v i x) t) := by
  have hbound (x y : Y) :
      timeLowerEnvelope M s (fun i => v i x) t ≤
        timeLowerEnvelope M s (fun i => v i y) t+(L:ℝ)*dist x y := by
    apply csSup_le (show ({-M} ∪ {a | ∃ i, s i < t ∧ a = v i x}).Nonempty from
      ⟨-M,Or.inl (mem_singleton _)⟩)
    rintro a (ha | ⟨i,hi,rfl⟩)
    · have hy := (abs_le.mp (timeLowerEnvelope_bounds hM s (fun i => v i y)
        (fun i => hv i y) t)).1
      have hp : 0 ≤ (L:ℝ)*dist x y := mul_nonneg L.coe_nonneg dist_nonneg
      simp only [mem_singleton_iff] at ha
      linarith
    · have hiY := sample_le_timeLowerEnvelope hM s (fun i => v i y) (fun i => hv i y) hi
      have hxy := (hL i).dist_le_mul x y
      rw [Real.dist_eq] at hxy
      linarith [le_abs_self (v i x-v i y)]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  apply abs_le.mpr
  have hxy := hbound x y
  have hyx := hbound y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

end RegularPointCoordinates

end

end OAI
