import OAI.MeasureTheory.Falconer.Geometry.TransverseGridCoordinates
import OAI.MeasureTheory.Falconer.Slicing.GaussianRowMap
import OAI.MeasureTheory.Falconer.Geometry.IntegerRectangle

namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

noncomputable def tripleRound (δ : ℝ) (x : Space 3) : ℤ × ℤ × ℤ :=
  (round (x 0/δ),round (x 1/δ),round (x 2/δ))

theorem round_mesh_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |t-δ*(round (t/δ):ℝ)| ≤ δ/2 := by
  have he : t-δ*(round (t/δ):ℝ) = δ*(t/δ-(round (t/δ):ℝ)) := by field_simp
  rw [he,abs_mul,abs_of_pos hδ]
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (t/δ)) hδ.le
  nlinarith

theorem tripleRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space 3) :
    dist x (tripleGridPoint δ (tripleRound δ x)) ≤ 3*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-tripleGridPoint δ (tripleRound δ x))
    (r := δ/2) (by
      intro i
      fin_cases i <;> exact round_mesh_error hδ _)
  norm_num only [Nat.cast_ofNat] at hh
  linarith

noncomputable def tripleIntegerBox (L : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(L:ℤ)) (L:ℤ)).product
    ((Finset.Icc (-(L:ℤ)) (L:ℤ)).product (Finset.Icc (-(L:ℤ)) (L:ℤ)))

theorem round_bound {δ R : ℝ} (hδ : 0 < δ) (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ))
    (t : ℝ) (ht : |t| ≤ R) : -(L:ℤ) ≤ round (t/δ) ∧ round (t/δ) ≤ (L:ℤ) := by
  have hh : |(round (t/δ):ℝ)| ≤ (L:ℝ) := by
    have hs := abs_sub_round (t/δ)
    have htri := abs_sub_le (round (t/δ):ℝ) (t/δ) 0
    rw [sub_zero,sub_zero,abs_sub_comm (round (t/δ):ℝ)] at htri
    have hd : |t/δ| ≤ R/δ := by
      rw [abs_div,abs_of_pos hδ]
      exact div_le_div_of_nonneg_right ht hδ.le
    linarith
  have hi : |round (t/δ)| ≤ (L:ℤ) := by exact_mod_cast hh
  exact abs_le.mp hi

theorem tripleRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space 3) (hx : ‖x‖ ≤ R) :
    tripleRound δ x ∈ tripleIntegerBox L := by
  have hb (i : Fin 3) : -(L:ℤ) ≤ round (x i/δ) ∧ round (x i/δ) ≤ (L:ℤ) :=
    round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 0),
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hb 1),Finset.mem_Icc.mpr (hb 2)⟩⟩

noncomputable def roundedTripleGrid (E : Set (Space 3)) (δ : ℝ) (L : ℕ) :
    Finset (ℤ × ℤ × ℤ) := by
  classical
  exact (tripleIntegerBox L).filter (fun z => ∃ x ∈ E, tripleRound δ x = z)

theorem roundedTripleGrid_mem {E : Set (Space 3)} {δ R : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ)) (hE : ∀ x ∈ E, ‖x‖ ≤ R)
    {x : Space 3} (hx : x ∈ E) : tripleRound δ x ∈ roundedTripleGrid E δ L := by
  classical
  exact Finset.mem_filter.mpr ⟨tripleRound_mem_box hδ L hL x (hE x hx),x,hx,rfl⟩

theorem roundedTripleGrid_original {E : Set (Space 3)} {δ : ℝ} {L : ℕ}
    {z : ℤ × ℤ × ℤ} (hz : z ∈ roundedTripleGrid E δ L) :
    ∃ x ∈ E, tripleRound δ x = z := by
  classical
  exact (Finset.mem_filter.mp hz).2

end Falconer

end OAI
