import OAI.GroupTheory.PolycyclicRecognition.Geometry.AffineProfileBoundary

namespace OAI

/-! # The contracted profile domains exhaust the interior cell -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

/-- Inverse dilation of a fixed interior point remains in the cell when
its scalar tends to one. No boundary regularity is required. -/
theorem eventually_mem_shrinking_cell
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {cell : Set W} {w : W} (hw : w ∈ interior cell)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (c : ℝ) :
    ∀ᶠ j in atTop, w ∈ (fun v => (1 - c * δ j) • v) '' cell := by
  have ht : Tendsto (fun j => 1 - c * δ j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hδ.const_mul c)
  have hv : Tendsto (fun j => (1 - c * δ j)⁻¹ • w) atTop (𝓝 w) := by
    simpa only [inv_one, one_smul] using (ht.inv₀ one_ne_zero).smul
      (tendsto_const_nhds (x := w))
  filter_upwards [hv.eventually (mem_interior_iff_mem_nhds.mp hw),
    ht.eventually_ne one_ne_zero] with j hj hn
  exact ⟨(1 - c * δ j)⁻¹ • w, hj, by dsimp only; rw [smul_smul, mul_inv_cancel₀ hn, one_smul]⟩

/-- Affine identities on contracted cells therefore give the eventual
interior identities used by the boundary and Haar diagonal arguments. -/
theorem eventually_affine_of_shrinking_cells
    {V W Y : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Add Y] (q : V → W) (cell : Set W) (f : ℕ → V → Y)
    (A : W → Y) (b : ℕ → Y) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (c : ℝ)
    (haff : ∀ j z, q z ∈ (fun w => (1 - c * δ j) • w) '' cell →
      f j z = A (q z) + b j) :
    ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, f j z = A (q z) + b j := by
  intro z hz
  exact (eventually_mem_shrinking_cell hz hδ c).mono (fun j hj => haff j z hj)

/-- The same exhaustion holds when each row is known affine only on the
open contracted cell, as in the local affinity theorem. -/
theorem eventually_affine_of_shrinking_interiors
    {V W Y : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [Add Y] (q : V → W) (cell : Set W) (f : ℕ → V → Y)
    (A : W → Y) (b : ℕ → Y) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (c : ℝ)
    (haff : ∀ j z, q z ∈ (fun w => (1 - c * δ j) • w) '' interior cell →
      f j z = A (q z) + b j) :
    ∀ z, q z ∈ interior cell → ∀ᶠ j in atTop, f j z = A (q z) + b j := by
  intro z hz
  have hz' : q z ∈ interior (interior cell) := by simpa only [interior_interior] using hz
  exact (eventually_mem_shrinking_cell hz' hδ c).mono (fun j hj => haff j z hj)

end PolycyclicRecognition

end

end OAI
