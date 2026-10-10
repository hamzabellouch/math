import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedRawDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolventModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatKernelModulus

namespace OAI

/-! Quantitative continuity needed by the six-coordinate finite-box
quadrature. Only the box radius enters the Gaussian modulus. -/

noncomputable section
namespace ContinuumCoulomb

theorem gaussian_box_modulus {freq L z w : ℝ} (hf : 0 ≤ freq)
    (hz : |z| ≤ L) (hw : |w| ≤ L) :
    |Real.exp (-freq * z ^ 2) - Real.exp (-freq * w ^ 2)| ≤
      2 * freq * L * |z - w| := by
  have he := HeatKernelModulus.exp_nonpositive_lipschitz
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf) (sq_nonneg z))
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf) (sq_nonneg w))
  have hid : -freq * z ^ 2 - (-freq * w ^ 2) = -freq * (z - w) * (z + w) := by ring
  rw [hid, abs_mul, abs_mul, abs_neg, abs_of_nonneg hf] at he
  have hs : |z + w| ≤ 2 * L := (abs_add_le z w).trans (by linarith)
  calc
    _ ≤ freq * |z - w| * |z + w| := he
    _ ≤ freq * |z - w| * (2 * L) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hf (abs_nonneg _))
    _ = _ := by ring

def splitRawDensity (freq : ℝ) (p : SplitPosition) : ℝ :=
  planarResolventMode p.1 ^ 2 * Real.exp (-freq * p.2 ^ 2)

theorem splitRawDensity_eq (freq : ℝ) (x : Position) :
    splitRawDensity freq (positionSplitCoordinates x) = localizedRawDensity freq x := rfl

theorem splitRawDensity_modulus {freq L : ℝ} (hf : 0 ≤ freq)
    (p q : SplitPosition) (hp : |p.2| ≤ L) (hq : |q.2| ≤ L) :
    |splitRawDensity freq p - splitRawDensity freq q| ≤
      64 * ‖p.1 - q.1‖ + 2 * freq * L * |p.2 - q.2| := by
  have hφ : planarResolventMode q.1 ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (sq_le_sq₀ (planarResolventMode_positive q.1).le zero_le_one).mpr
        (planarResolventMode_le_one q.1)
  have he : Real.exp (-freq * p.2 ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hf) (sq_nonneg _))
  have hid : splitRawDensity freq p - splitRawDensity freq q =
      (planarResolventMode p.1 ^ 2 - planarResolventMode q.1 ^ 2) *
        Real.exp (-freq * p.2 ^ 2) +
      planarResolventMode q.1 ^ 2 *
        (Real.exp (-freq * p.2 ^ 2) - Real.exp (-freq * q.2 ^ 2)) := by
    unfold splitRawDensity
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (sq_nonneg (planarResolventMode q.1))]
  have h1 := (mul_le_of_le_one_right (abs_nonneg _) he).trans
    (planarResolventMode_square_norm_sub p.1 q.1)
  have h2 := (mul_le_of_le_one_left (abs_nonneg _) hφ).trans
    (gaussian_box_modulus hf hp hq)
  exact add_le_add h1 h2

theorem positionSplit_planar_norm_sub_le (x y : Position) :
    ‖(positionSplitCoordinates x).1 - (positionSplitCoordinates y).1‖ ≤ ‖x - y‖ := by
  have h := positionSplitCoordinates_norm_sq (x - y)
  rw [map_sub] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
    nlinarith [sq_nonneg ((positionSplitCoordinates x).2 - (positionSplitCoordinates y).2)])

theorem positionSplit_vertical_norm_sub_le (x y : Position) :
    |(positionSplitCoordinates x).2 - (positionSplitCoordinates y).2| ≤ ‖x - y‖ := by
  have h := positionSplitCoordinates_norm_sq (x - y)
  rw [map_sub] at h
  simp only [Prod.fst_sub, Prod.snd_sub] at h
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg ‖(positionSplitCoordinates x).1 - (positionSplitCoordinates y).1‖]

theorem localizedRawDensity_box_modulus {freq L : ℝ} (hf : 0 ≤ freq)
    (x y : Position) (hx : |(positionSplitCoordinates x).2| ≤ L)
    (hy : |(positionSplitCoordinates y).2| ≤ L) :
    |localizedRawDensity freq x - localizedRawDensity freq y| ≤
      (64 + 2 * freq * L) * ‖x - y‖ := by
  have hL : 0 ≤ L := (abs_nonneg _).trans hx
  have h := splitRawDensity_modulus hf (positionSplitCoordinates x) (positionSplitCoordinates y) hx hy
  rw [splitRawDensity_eq, splitRawDensity_eq] at h
  apply h.trans
  calc
    _ ≤ 64 * ‖x - y‖ + 2 * freq * L * ‖x - y‖ := by
      gcongr
      · exact positionSplit_planar_norm_sub_le x y
      · exact positionSplit_vertical_norm_sub_le x y
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
