import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

noncomputable section
open Set

namespace CylinderCovering.RadialRiemann

theorem step_affine (a b c r : ℝ) (N : ℕ) :
    step (c + r * a) (c + r * b) N = r * step a b N := by
  unfold step
  ring

theorem point_affine (a b c r : ℝ) (N i : ℕ) :
    point (c + r * a) (c + r * b) N i = c + r * point a b N i := by
  unfold point
  rw [step_affine]
  ring

theorem affine_mem_cell_iff (a b c : ℝ) {r : ℝ} (hr : 0 < r)
    (N : ℕ) (i : Fin N) (s : ℝ) :
    c + r * s ∈ cell (c + r * a) (c + r * b) N i ↔
      s ∈ cell a b N i := by
  simp only [cell, mem_Icc, point_affine, add_le_add_iff_left,
    mul_le_mul_iff_right₀ hr]

theorem image_cell_affine (a b c : ℝ) {r : ℝ} (hr : 0 < r)
    (N : ℕ) (i : Fin N) :
    (fun s => c + r * s) '' cell a b N i =
      cell (c + r * a) (c + r * b) N i := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (affine_mem_cell_iff a b c hr N i s).2 hs
  · intro hx
    have heq : c + r * ((x - c) / r) = x := by
      field_simp
      ring
    refine ⟨(x - c) / r, ?_, heq⟩
    apply (affine_mem_cell_iff a b c hr N i ((x - c) / r)).1
    rwa [heq]

theorem isTagged_affine_iff (a b c : ℝ) {r : ℝ} (hr : 0 < r)
    (N : ℕ) (tag : Fin N → ℝ) :
    IsTagged (c + r * a) (c + r * b) N (fun i => c + r * tag i) ↔
      IsTagged a b N tag := by
  unfold IsTagged
  exact forall_congr' fun i => affine_mem_cell_iff a b c hr N i (tag i)

theorem IsTagged.affine {a b : ℝ} {N : ℕ} {tag : Fin N → ℝ}
    (htag : IsTagged a b N tag) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    IsTagged (c + r * a) (c + r * b) N (fun i => c + r * tag i) :=
  (isTagged_affine_iff a b c hr N tag).2 htag

theorem IsTagged.affine_inverse {a b c : ℝ} {r : ℝ} (hr : 0 < r)
    {N : ℕ} {tag : Fin N → ℝ}
    (htag : IsTagged (c + r * a) (c + r * b) N tag) :
    IsTagged a b N (fun i => (tag i - c) / r) := by
  apply (isTagged_affine_iff a b c hr N _).1
  convert htag using 1
  funext i
  field_simp
  ring

theorem capMax_affine (R : ℝ → ℝ) (a b c : ℝ) {r : ℝ} (hr : 0 < r)
    (N : ℕ) (i : Fin N) :
    capMax R (c + r * a) (c + r * b) N i =
      capMax (fun s => R (c + r * s)) a b N i := by
  unfold capMax
  rw [← image_cell_affine a b c hr N i, image_image]

theorem IsTagged.div_pos {b : ℝ} (hb : 0 < b) {N : ℕ} {tag : Fin N → ℝ}
    (htag : IsTagged (-b) b N tag) :
    IsTagged (-1) 1 N (fun i => tag i / b) := by
  have h : IsTagged ((0 : ℝ) + b * (-1)) (0 + b * 1) N tag := by
    simpa using htag
  simpa using h.affine_inverse hb

theorem div_mem_symmetric_cell_iff {b : ℝ} (hb : 0 < b)
    (N : ℕ) (i : Fin N) (s : ℝ) :
    s / b ∈ cell (-1) 1 N i ↔ s ∈ cell (-b) b N i := by
  have h := affine_mem_cell_iff (-1) 1 0 hb N i (s / b)
  simpa [mul_div_cancel₀ s (ne_of_gt hb)] using h.symm

theorem barycentric_mem_cell_iff (N : ℕ) (i : Fin N) (t : ℝ) :
    2 * t - 1 ∈ cell (-1) 1 N i ↔ t ∈ cell 0 1 N i := by
  have h := affine_mem_cell_iff 0 1 (-1) (by norm_num : (0 : ℝ) < 2) N i t
  simpa only [mul_zero, add_zero, mul_one,
    show (-1 : ℝ) + 2 = 1 by norm_num,
    show (-1 : ℝ) + 2 * t = 2 * t - 1 by ring] using h

theorem IsTagged.barycentric {N : ℕ} {tag : Fin N → ℝ}
    (htag : IsTagged 0 1 N tag) :
    IsTagged (-1) 1 N (fun i => 2 * tag i - 1) := by
  intro i
  exact (barycentric_mem_cell_iff N i (tag i)).2 (htag i)

end CylinderCovering.RadialRiemann

end

end OAI
