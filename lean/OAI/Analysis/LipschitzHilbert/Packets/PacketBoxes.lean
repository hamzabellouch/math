import OAI.Analysis.LipschitzHilbert.Estimates.EnvelopeSynthesis
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! Actual center-box assignment on a reference line and exact grouping
of the finite Schwartz synthesis. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def packetBoxIndex (u y r W x z : ℝ) : ℤ × ℤ :=
  (⌊(x - u) / r⌋, ⌊(z - y) / W⌋)

theorem floor_box_distance (u r x : ℝ) (hr : 0 < r) :
    |x - (u + r * (⌊(x - u) / r⌋ : ℤ))| ≤ r := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le ((x - u) / r)) hr.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x - u) / r)) hr
  rw [div_mul_cancel₀ _ hr.ne'] at hlo hhi
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem packetBoxIndex_horizontal (u y r W x z : ℝ) (hr : 0 < r) :
    |x - (u + r * (packetBoxIndex u y r W x z).1)| ≤ r :=
  floor_box_distance u r x hr

theorem packetBoxIndex_vertical (u y r W x z : ℝ) (hW : 0 < W) :
    |z - (y + W * (packetBoxIndex u y r W x z).2)| ≤ W :=
  floor_box_distance y W z hW

def packetBoxSynthesis {ι : Type*} [Fintype ι] (index : ι → ℤ × ℤ)
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) : SchwartzMap ℝ ℂ :=
  ∑ i, if index i = b then c i • f i else 0

theorem packetSynthesis_eq_sum_boxes_of_mem {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ)
    (boxes : Finset (ℤ × ℤ)) (hboxes : ∀ i, index i ∈ boxes) :
    packetSynthesis c f = ∑ b ∈ boxes, packetBoxSynthesis index c f b := by
  classical
  unfold packetSynthesis packetBoxSynthesis
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (index i)]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · intro hi
    exact (hi (hboxes i)).elim

theorem packetSynthesis_eq_sum_boxes {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) :
    packetSynthesis c f = ∑ b ∈ Finset.univ.image index, packetBoxSynthesis index c f b := by
  classical
  exact packetSynthesis_eq_sum_boxes_of_mem index c f _
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem packetBoxSynthesis_eq_subtype {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) :
    packetBoxSynthesis index c f b =
      packetSynthesis (fun i : {i // index i = b} => c i) (fun i => f i) := by
  classical
  unfold packetBoxSynthesis packetSynthesis
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun i => index i = b)) (by simp) (fun i => c i • f i)

end LipschitzHilbert

end

end OAI
