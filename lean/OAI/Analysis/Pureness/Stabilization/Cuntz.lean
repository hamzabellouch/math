import OAI.Analysis.Pureness.Stabilization.Cuts
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Tactic.NoncommRing

namespace OAI
noncomputable section
open scoped Topology NNReal
open Filter
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def CuntzBelow (a b : Positive A) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ v : A, ‖star v * b.1 * v - a.1‖ < ε

omit [PartialOrder A] [StarOrderedRing A] in
theorem conjugate_norm_le (v x : A) : ‖star v * x * v‖ ≤ ‖v‖ ^ 2 * ‖x‖ := by
  calc
    ‖star v * x * v‖ ≤ ‖star v * x‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ (‖star v‖ * ‖x‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖v‖ ^ 2 * ‖x‖ := by rw [norm_star]; ring

namespace CuntzBelow

omit [StarOrderedRing A] in
theorem zero (b : Positive A) : CuntzBelow Positive.zero b := by
  intro ε hε
  exact ⟨0, by simpa [Positive.zero] using hε⟩

theorem refl (a : Positive A) : CuntzBelow a a := by
  intro ε hε
  let U := CStarAlgebra.approximateUnit A
  have hU := CStarAlgebra.increasingApproximateUnit A
  have hl : ∀ᶠ u in U, ‖a.1 * u - a.1‖ < ε / 2 := by
    have ht := ((hU.tendsto_mul_left a.1).sub (tendsto_const_nhds (x := a.1))).norm
    have hzero : Tendsto (fun u => ‖a.1 * u - a.1‖) U (𝓝 0) := by simpa using ht
    exact (tendsto_order.mp hzero).2 (ε / 2) (by linarith)
  have hr : ∀ᶠ u in U, ‖u * a.1 - a.1‖ < ε / 2 := by
    have ht := ((hU.tendsto_mul_right a.1).sub (tendsto_const_nhds (x := a.1))).norm
    have hzero : Tendsto (fun u => ‖u * a.1 - a.1‖) U (𝓝 0) := by simpa using ht
    exact (tendsto_order.mp hzero).2 (ε / 2) (by linarith)
  obtain ⟨u, hu, hstar, hul, hur⟩ :=
    (hU.eventually_norm.and (hU.eventually_star_eq.and (hl.and hr))).exists
  refine ⟨u, ?_⟩
  rw [hstar]
  have heq : u * a.1 * u - a.1 = u * (a.1 * u - a.1) + (u * a.1 - a.1) := by
    noncomm_ring
  rw [heq]
  have hnorm : ‖u * (a.1 * u - a.1)‖ ≤ ‖a.1 * u - a.1‖ :=
    (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (a.1 * u - a.1)])
  exact (norm_add_le _ _).trans_lt (by linarith)

omit [StarOrderedRing A] in
theorem eq_zero {a : Positive A} (h : CuntzBelow a Positive.zero) : a.1 = 0 := by
  by_contra ha
  obtain ⟨v, hv⟩ := h ‖a.1‖ (norm_pos_iff.mpr ha)
  simp [Positive.zero] at hv

omit [StarOrderedRing A] in
theorem trans {a b c : Positive A} (hab : CuntzBelow a b) (hbc : CuntzBelow b c) :
    CuntzBelow a c := by
  intro ε hε
  obtain ⟨v, hv⟩ := hab (ε / 2) (by linarith)
  let C := ‖v‖ ^ 2
  have hC : 0 ≤ C := sq_nonneg _
  let δ := ε / (2 * (C + 1))
  have hd : 0 < 2 * (C + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hd
  obtain ⟨w, hw⟩ := hbc δ hδ
  have hδeq : δ * (2 * (C + 1)) = ε := div_mul_cancel₀ ε hd.ne'
  have hCδ : C * δ ≤ ε / 2 := by nlinarith
  have hbound : C * ‖star w * c.1 * w - b.1‖ ≤ ε / 2 :=
    (mul_le_mul_of_nonneg_left hw.le hC).trans hCδ
  refine ⟨w * v, ?_⟩
  have heq : star (w * v) * c.1 * (w * v) - a.1 =
      star v * (star w * c.1 * w - b.1) * v + (star v * b.1 * v - a.1) := by
    rw [star_mul]
    noncomm_ring
  rw [heq]
  calc
    ‖star v * (star w * c.1 * w - b.1) * v + (star v * b.1 * v - a.1)‖ ≤
        ‖star v * (star w * c.1 * w - b.1) * v‖ + ‖star v * b.1 * v - a.1‖ :=
      norm_add_le _ _
    _ ≤ C * ‖star w * c.1 * w - b.1‖ + ‖star v * b.1 * v - a.1‖ :=
      add_le_add (conjugate_norm_le _ _) le_rfl
    _ < ε := by linarith

omit [StarOrderedRing A] in
theorem of_tendsto {a : Positive A} (aₙ : ℕ → Positive A) (b : Positive A)
    (ha : Tendsto aₙ atTop (𝓝 a)) (h : ∀ n, CuntzBelow (aₙ n) b) : CuntzBelow a b := by
  intro ε hε
  have ht := tendsto_subtype_rng.mp ha
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht) (ε / 2) (by linarith)
  obtain ⟨v, hv⟩ := h N (ε / 2) (by linarith)
  refine ⟨v, ?_⟩
  have hd : ‖(aₙ N).1 - a.1‖ < ε / 2 := by simpa [dist_eq_norm] using hN N le_rfl
  have heq : star v * b.1 * v - a.1 =
      (star v * b.1 * v - (aₙ N).1) + ((aₙ N).1 - a.1) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem of_cuts {a b : Positive A}
    (h : ∀ ε : ℝ≥0, 0 < ε → CuntzBelow (Positive.cut ε a) b) : CuntzBelow a b := by
  let ε : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  apply of_tendsto (fun n => Positive.cut (ε n) a) b
  · apply Positive.tendsto_cut
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  · intro n
    apply h
    dsimp [ε]
    positivity

end CuntzBelow
end CuntzTrace

end

end OAI
