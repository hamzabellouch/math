import OAI.MeasureTheory.Falconer.Radial.VanishingSlabs
import OAI.MeasureTheory.Falconer.Graphs.AllDimensionalGraphGeometry

namespace OAI

/-! # Affine slabs with a common point and nearby normal directions -/

namespace Falconer
open Set NormedSpace
variable {d : ℕ}

noncomputable def normalDistance (u v : Space d) : ℝ := min ‖u-v‖ ‖u+v‖

theorem affine_slab_cluster {u v x y : Space d} {a b M r τ : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hτ : normalDistance u v ≤ τ)
    (hux : |inner ℝ u x-a| ≤ r) (hvx : |inner ℝ v x-b| ≤ r)
    (hvy : |inner ℝ v y-b| ≤ r) :
    |inner ℝ u y-a| ≤ 2*M*τ+3*r := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  have hxy : ‖y-x‖ ≤ 2*M := (norm_sub_le y x).trans (by linarith only [hx,hy])
  have hvxy : |inner ℝ v (y-x)| ≤ 2*r := by
    rw [inner_sub_right]
    have he : inner ℝ v y-inner ℝ v x = (inner ℝ v y-b)-(inner ℝ v x-b) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith only [hvx,hvy])
  have huxy : |inner ℝ u (y-x)| ≤ 2*M*τ+2*r := by
    have helper (w : Space d) (hw : ‖u-w‖ ≤ τ)
        (hwi : |inner ℝ w (y-x)| ≤ 2*r) :
        |inner ℝ u (y-x)| ≤ 2*M*τ+2*r := by
      have he : inner ℝ u (y-x) = inner ℝ (u-w) (y-x)+inner ℝ w (y-x) := by
        rw [inner_sub_left]; ring
      rw [he]
      apply (abs_add_le _ _).trans
      have hb : |inner ℝ (u-w) (y-x)| ≤ τ*(2*M) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul hw hxy (norm_nonneg _) ((norm_nonneg _).trans hw))
      linarith only [hb,hwi]
    rcases (min_le_iff.mp hτ) with h | h
    · exact helper v h hvxy
    · apply helper (-v) (by simpa only [sub_neg_eq_add] using h)
      simpa only [inner_neg_left,abs_neg] using hvxy
  have he : inner ℝ u y-a = inner ℝ u (y-x)+(inner ℝ u x-a) := by
    rw [inner_sub_right]; ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [huxy,hux])

end Falconer

end OAI
