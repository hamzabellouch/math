import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanDerivativeBounds

namespace OAI

/-! The two-dimensional torus distance needed for support separation.
Only the centered representative and its elementary triangle inequality
are used; no geometric quotient machinery is required. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows

def centeredRepresentative (x : Plane) : Plane :=
  letI := ShearFlows.twoAtLeastTwo
  fun j => x j - (⌊x j + 1 / 2⌋ : ℤ)

def torusNorm (x : Plane) : ℝ := ‖planeCoordinates.symm (centeredRepresentative x)‖

theorem centered_nearest_integer (r : ℝ) (k : ℤ) :
    |r - (⌊r + 1 / 2⌋ : ℤ)| ≤ |r - (k : ℝ)| := by
  have hlo := Int.floor_le (r + 1 / 2)
  have hhi := Int.lt_floor_add_one (r + 1 / 2)
  rcases lt_trichotomy k ⌊r + 1 / 2⌋ with hk | hk | hk
  · have hki : (k : ℝ) + 1 ≤ (⌊r + 1 / 2⌋ : ℤ) := by
      exact_mod_cast Int.add_one_le_iff.mpr hk
    rw [abs_of_nonneg (show 0 ≤ r - (k : ℝ) by linarith)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [hk]
  · have hki : (⌊r + 1 / 2⌋ : ℤ) + (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Int.add_one_le_iff.mpr hk
    rw [abs_of_nonpos (show r - (k : ℝ) ≤ 0 by linarith)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem torusNorm_sq (x : Plane) : torusNorm x ^ 2 = torusDistanceSq x := by
  rw [torusNorm, EuclideanSpace.real_norm_sq_eq]
  rfl

theorem torusNorm_nonneg (x : Plane) : 0 ≤ torusNorm x := norm_nonneg _

theorem torusNorm_le_lattice (x : Plane) (k : Fin 2 → ℤ) :
    torusNorm x ≤ ‖planeCoordinates.symm (x - fun j => (k j : ℝ))‖ := by
  have hsq : torusNorm x ^ 2 ≤
      ‖planeCoordinates.symm (x - fun j => (k j : ℝ))‖ ^ 2 := by
    rw [torusNorm_sq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change (x j - (⌊x j + 1 / 2⌋ : ℤ)) ^ 2 ≤ (x j - (k j : ℝ)) ^ 2
    exact (sq_le_sq).mpr (centered_nearest_integer (x j) (k j))
  nlinarith [torusNorm_nonneg x, norm_nonneg (planeCoordinates.symm (x - fun j => (k j : ℝ)))]

theorem torusNorm_le_norm (x : Plane) : torusNorm x ≤ ‖planeCoordinates.symm x‖ := by
  have h := torusNorm_le_lattice x (fun _ => 0)
  have hz : (fun _ : Fin 2 => ((0 : ℤ) : ℝ)) = (0 : Plane) := by
    ext j
    simp only [Int.cast_zero, Pi.zero_apply]
  simpa only [hz, sub_zero] using h

theorem torusNorm_add_le (x y : Plane) : torusNorm (x + y) ≤ torusNorm x + torusNorm y := by
  let k : Fin 2 → ℤ := fun j => ⌊x j + 1 / 2⌋ + ⌊y j + 1 / 2⌋
  have he : (x + y) - (fun j => (k j : ℝ)) =
      centeredRepresentative x + centeredRepresentative y := by
    ext j
    simp only [Pi.add_apply, Pi.sub_apply, k, Int.cast_add, centeredRepresentative]
    ring
  calc
    _ ≤ ‖planeCoordinates.symm ((x + y) - fun j => (k j : ℝ))‖ := torusNorm_le_lattice _ k
    _ = ‖planeCoordinates.symm (centeredRepresentative x) +
        planeCoordinates.symm (centeredRepresentative y)‖ := by rw [he, map_add]
    _ ≤ _ := norm_add_le _ _

theorem torusNorm_neg (x : Plane) : torusNorm (-x) = torusNorm x := by
  have h (y : Plane) : torusNorm (-y) ≤ torusNorm y := by
    let k : Fin 2 → ℤ := fun j => -⌊y j + 1 / 2⌋
    have he : (-y) - (fun j => (k j : ℝ)) = -centeredRepresentative y := by
      ext j
      simp only [Pi.neg_apply, Pi.sub_apply, k, Int.cast_neg, centeredRepresentative]
      ring
    calc
      _ ≤ ‖planeCoordinates.symm ((-y) - fun j => (k j : ℝ))‖ := torusNorm_le_lattice _ k
      _ = torusNorm y := by rw [he, map_neg, norm_neg]; rfl
  exact le_antisymm (h x) (by simpa only [neg_neg] using h (-x))

theorem torus_separation {p x y : Plane} {d ε : ℝ}
    (hnear : torusNorm (y - p) ≤ ε) (hfar : 2 * d ≤ torusNorm (p - x))
    (hε : ε ≤ d) : d ≤ torusNorm (x - y) := by
  have htri := torusNorm_add_le (p - y) (y - x)
  have he : (p - y) + (y - x) = p - x := by abel
  have he₁ : p - y = -(y - p) := by abel
  have he₂ : y - x = -(x - y) := by abel
  rw [he, he₁, he₂, torusNorm_neg, torusNorm_neg] at htri
  linarith

end ForcedComputation.VelocityDetector

end

end OAI
