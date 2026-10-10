import OAI.Geometry.CylinderCovering.Simplex.Projection

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering

theorem simplex_homothety_volume {d : ℕ} (q : Euclidean d) {r : ℝ}
    (hr : 0 ≤ r) (S : Set (Euclidean d)) :
    volume.real (AffineMap.homothety q r '' S) = r ^ d * volume.real S := by
  change (volume (AffineMap.homothety q r '' S)).toReal = _
  rw [Measure.addHaar_image_homothety]
  simp [ENNReal.toReal_mul, abs_of_nonneg (pow_nonneg hr d),
    ENNReal.toReal_ofReal (pow_nonneg hr d), Measure.real]

theorem affine_simplex_overlap_volume {d : ℕ}
    (p : AffineBasis (Fin (d + 1)) ℝ (Euclidean d)) {u : Euclidean d}
    (hu : u ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (hsm : s * (∑ i, max 0 (-(p.coord i).linear u)) < 1) :
    volume.real {x | x ∈ convexHull ℝ (range p) ∧
        x + s • u ∈ convexHull ℝ (range p)} =
      (1 - s * (∑ i, max 0 (-(p.coord i).linear u))) ^ d *
        volume.real (convexHull ℝ (range p)) := by
  obtain ⟨q, _, _, hhom⟩ := SimplexChord.affine_intersection_homothety p hu
  rw [hhom s hs hsm]
  exact simplex_homothety_volume q (sub_nonneg.mpr hsm.le) _

theorem affine_simplex_overlap_volume_lt_reciprocal {d : ℕ}
    (p : AffineBasis (Fin (d + 1)) ℝ (Euclidean d)) {u : Euclidean d}
    (hu : u ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (hsM : s < (∑ i, max 0 (-(p.coord i).linear u))⁻¹) :
    volume.real {x | x ∈ convexHull ℝ (range p) ∧
        x + s • u ∈ convexHull ℝ (range p)} =
      (1 - s * (∑ i, max 0 (-(p.coord i).linear u))) ^ d *
        volume.real (convexHull ℝ (range p)) := by
  have hM : 0 < ∑ i, max 0 (-(p.coord i).linear u) :=
    SimplexChord.negative_mass_pos _ (SimplexChord.sum_coord_linear_eq_zero p u)
      (SimplexChord.coord_linear_ne_zero p hu)
  apply affine_simplex_overlap_volume p hu hs
  exact (lt_div_iff₀ hM).mp (by simpa only [one_div] using hsM)

theorem translated_intersection_eq {d : ℕ} (S : Set (Euclidean d))
    (u : Euclidean d) (s : ℝ) :
    {x | x ∈ S ∧ x + s • u ∈ S} = S ∩ (fun y => y - s • u) '' S := by
  ext x
  constructor
  · rintro ⟨hx, hxu⟩
    exact ⟨hx, x + s • u, hxu, add_sub_cancel_right x (s • u)⟩
  · rintro ⟨hx, y, hy, hxy⟩
    refine ⟨hx, ?_⟩
    rw [← hxy]
    simpa using hy

theorem simplex_overlap_volume {d : ℕ} (v : Fin (d + 1) → Euclidean d)
    (hv : AffineIndependent ℝ v) {u : Euclidean d} (hu : ‖u‖ = 1)
    {s : ℝ} (hs : 0 ≤ s) (hsL : s < longestChord (simplexCarrier v) u) :
    volume.real {x | x ∈ simplexCarrier v ∧ x + s • u ∈ simplexCarrier v} =
      (1 - s / longestChord (simplexCarrier v) u) ^ d *
        volume.real (simplexCarrier v) := by
  obtain ⟨hL, _, _, _, hhom⟩ := simplex_chord_data v hv hu
  rw [hhom s hs hsL]
  apply simplex_homothety_volume
  exact sub_nonneg.mpr ((div_le_one hL).mpr hsL.le)

theorem tetrahedron_overlap_volume (v : Fin 4 → Euclidean 3)
    (hv : AffineIndependent ℝ v) {u : Euclidean 3} (hu : ‖u‖ = 1)
    {s : ℝ} (hs : 0 ≤ s) (hsL : s < longestChord (simplexCarrier v) u) :
    volume.real {x | x ∈ simplexCarrier v ∧ x + s • u ∈ simplexCarrier v} =
      (1 - s / longestChord (simplexCarrier v) u) ^ 3 *
        volume.real (simplexCarrier v) :=
  simplex_overlap_volume v hv hu hs hsL

theorem tetrahedron_translated_overlap_volume (v : Fin 4 → Euclidean 3)
    (hv : AffineIndependent ℝ v) {u : Euclidean 3} (hu : ‖u‖ = 1)
    {s : ℝ} (hs : 0 ≤ s) (hsL : s < longestChord (simplexCarrier v) u) :
    volume.real (simplexCarrier v ∩ (fun y => y - s • u) '' simplexCarrier v) =
      (1 - s / longestChord (simplexCarrier v) u) ^ 3 *
        volume.real (simplexCarrier v) := by
  rw [← translated_intersection_eq]
  exact tetrahedron_overlap_volume v hv hu hs hsL

end CylinderCovering

end

end OAI
