import OAI.Analysis.MetricEntropy.ConvexBody
import OAI.Analysis.MetricEntropy.PolarCover
import OAI.Analysis.MetricEntropy.CoordinateTransport
import Mathlib.Tactic.Linarith

namespace OAI

universe uX uY uι

/-!
# The actual matrix-to-body conversion

The separated points are the actual three-times-scaled rows. The primal
minimum has a finite-cover witness from compactness, and the dual cover has
actual coefficient-ball centers with exactly the approximation-list count.
The final wrapper uses a coordinate linear homeomorphism to obtain `Fin n`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped Pointwise

variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]

/-- A separated row family supplies the exact primal packing lower bound. -/
theorem matrixBody_primal_lower (g : Y → X → ℝ) (t : ℝ)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|) :
    Fintype.card X ≤ coveringNumber (matrixBody g t) (cube Y) := by
  apply card_le_coveringNumber_cube (fun x => (3 : ℝ) • row g x)
    (matrixBody_three_row_mem g t)
  · intro x x' hne
    obtain ⟨y, hy⟩ := hsep x x' hne
    refine ⟨y, ?_⟩
    change 2 < |3 * g y x - 3 * g y x'|
    rw [← mul_sub, abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    linarith
  · exact coverable_cube_of_isCompact (isCompact_matrixBody g t)

/-- Increasing a positive polar scale increases the actual covering body. -/
theorem smul_polar_mono {ι : Type uι} [Fintype ι]
    (K : Set (RealSpace ι)) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    c • polar K ⊆ d • polar K := by
  intro δ hδ
  apply (mem_smul_polar_iff K δ (lt_of_lt_of_le hc hcd)).mpr
  intro z hz
  exact le_trans ((mem_smul_polar_iff K δ hc).mp hδ z hz) hcd

/-- The same finite polar cover is valid at every larger positive scale. -/
theorem polar_cover_enlarge {ι : Type uι} [Fintype ι]
    (K : Set (RealSpace ι)) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hfin : Coverable (polar (cube ι)) (c • polar K)) :
    Coverable (polar (cube ι)) (d • polar K) ∧
      coveringNumber (polar (cube ι)) (d • polar K) ≤
        coveringNumber (polar (cube ι)) (c • polar K) := by
  have hsubset := smul_polar_mono K hc hcd
  exact ⟨hfin.mono_right hsubset, coveringNumber_mono_right hsubset hfin⟩

/-- Complete geometric conversion for actual real columns. No compactness,
support, polar-cover, or covering-minimum hypothesis is assumed. -/
theorem matrix_to_body [Nonempty X] (g : Y → X → ℝ) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    IsSymmetricConvexBody (matrixBody g t) ∧
      IsSymmetricConvexBody (cube Y) ∧
      Coverable (matrixBody g t) (cube Y) ∧
      Coverable (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t)) ∧
      Fintype.card X ≤ coveringNumber (matrixBody g t) (cube Y) ∧
      coveringNumber (polar (cube Y))
        ((6 * ε + 2 * t) • polar (matrixBody g t)) ≤ A.card := by
  exact ⟨matrixBody_isSymmetricConvexBody g t ht, cube_isSymmetricConvexBody,
    coverable_cube_of_isCompact (isCompact_matrixBody g t),
    cube_polar_coverable g hε ht A hA, matrixBody_primal_lower g t hsep,
    polar_coveringNumber_le g hε ht A hA⟩

/-- The actual geometric conversion in the ordinary positive dimension
`card Y`, with all covering centers transported in the same ambient space. -/
theorem matrix_to_body_fin [Nonempty X] [Nonempty Y]
    (g : Y → X → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    0 < Fintype.card Y ∧
      ∃ K : Set (RealSpace (Fin (Fintype.card Y))),
        IsSymmetricConvexBody K ∧
        IsSymmetricConvexBody (cube (Fin (Fintype.card Y))) ∧
        Coverable K (cube (Fin (Fintype.card Y))) ∧
        Coverable (polar (cube (Fin (Fintype.card Y)))) ((6 * ε + 2 * t) • polar K) ∧
        Fintype.card X ≤ coveringNumber K (cube (Fin (Fintype.card Y))) ∧
        coveringNumber (polar (cube (Fin (Fintype.card Y))))
          ((6 * ε + 2 * t) • polar K) ≤ A.card := by
  obtain ⟨hK, _, _, hdual, hlo, hhi⟩ := matrix_to_body g hε ht hsep A hA
  let K := coordinatesToFin (ι := Y) '' matrixBody g t
  have hK' : IsSymmetricConvexBody K :=
    (coordinatesToFin_body_iff (matrixBody g t)).mpr hK
  refine ⟨coordinate_dimension_pos, K, hK', cube_isSymmetricConvexBody,
    coverable_cube_of_isCompact hK'.isCompact, ?_, ?_, ?_⟩
  · have htransport := (coverable_coordinate_image (Fintype.equivFin Y)
      (polar (cube Y)) ((6 * ε + 2 * t) • polar (matrixBody g t))).mpr hdual
    rw [coordinate_polar, coordinate_cube, coordinate_image_smul, coordinate_polar]
      at htransport
    exact htransport
  · simpa only [K, coordinatesToFin_coveringNumber_cube] using hlo
  · simpa only [K, coordinatesToFin_coveringNumber_polar_cube] using hhi

end MetricEntropyDuality

end

end OAI
