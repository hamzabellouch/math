import OAI.MeasureTheory.Falconer.Slicing.GaussianKernelCoordinates
import OAI.MeasureTheory.Falconer.Slicing.SliceTubeGeometry

namespace OAI

/-! # Original tube labels and active anchors for Gaussian row slices -/

namespace Falconer
variable {d h : ℕ}

theorem gaussian_active_anchor (A : Fin h → Space d) (z : Space h)
    {w : Sphere d} {x a : Space d} {δ ε L M : ℝ} (_hM : 0 ≤ M)
    (hA : ∀ i, ‖A i‖ ≤ M) (hw : w ∈ gaussianDirectionBand A δ)
    (hx : x ∈ gaussianPointBand A z δ)
    (htube : ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε)
    (hlength : |inner ℝ (w:Space d) (x-a)| ≤ L) :
    a ∈ gaussianPointBand A z (δ+L*δ+ε*M) := by
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have he : a = x-t • (w:Space d)-e := by dsimp [t,e,perpendicularPart]; module
  intro i
  have hi : inner ℝ a (A i)-z i =
      (inner ℝ x (A i)-z i)-t*inner ℝ (w:Space d) (A i)-inner ℝ e (A i) := by
    rw [he,inner_sub_left,inner_sub_left,real_inner_smul_left]
    ring
  have ht : |t*inner ℝ (w:Space d) (A i)| ≤ L*δ := by
    rw [abs_mul]
    exact mul_le_mul hlength (hw i) (abs_nonneg _) ((abs_nonneg _).trans hlength)
  have hp : |inner ℝ e (A i)| ≤ ε*M :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul htube (hA i) (norm_nonneg _)
      ((norm_nonneg _).trans htube))
  rw [hi]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (add_le_add (add_le_add (hx i) ht) hp)

theorem gaussian_projected_tube_width (A : Fin h → Space d)
    {w : Sphere d} {δ K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hδ : K*((h:ℝ)*δ) < 1) (hw : w ∈ gaussianDirectionBand A δ) (x a : Space d) :
    ‖perpendicularPart (NormedSpace.normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
      ((gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection a)‖ ≤
      ‖perpendicularPart (w:Space d) (x-a)‖ :=
  slice_projected_tube_width _ hδ (gaussian_direction_band_kernel_distance A hK hbound hw) x a

end Falconer

end OAI
