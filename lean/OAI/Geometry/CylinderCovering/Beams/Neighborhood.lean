import OAI.Geometry.CylinderCovering.Beams.NeighborhoodDefinitions
import OAI.Geometry.CylinderCovering.Beams.Algebra

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.BeamNeighborhood

lemma radial_cancellation (a p m : ℝ) :
    velocity a p - velocity a m =
      (-2*a*(2-a)*(p-m)) • radial p + (a*(2-a)*(p-m)^2) • transverse := by
  ext i
  fin_cases i
  · simpa [velocity, radial, transverse] using BeamAlgebra.radial_cancellation_first a (2-a) p m
  · simpa [velocity, radial, transverse, sub_eq_add_neg] using BeamAlgebra.radial_cancellation_second a (2-a) p m

lemma intercept_decomposition (a p m h t : ℝ) :
    intercept a p m h t =
      (h-2*a*(2-a)*(p-m)*t) • radial p + (a*(2-a)*(p-m)^2*t) • transverse := by
  rw [intercept, radial_cancellation]
  module

lemma transverse_norm_le : ‖transverse‖ ≤ 2 := by
  have h : ‖transverse‖^2 = 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [transverse, Fin.sum_univ_two]
  nlinarith [norm_nonneg transverse]

lemma shortening_bounds {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2) :
    0 ≤ a*(2-a) ∧ a*(2-a) ≤ 1 := by
  constructor
  · exact mul_nonneg ha (by linarith)
  · nlinarith [sq_nonneg (a-1)]

lemma midpoint_radial_error {a p m t δ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hδ : 0 ≤ δ) (hp : |p-m| ≤ δ/2) (ht : |t| ≤ 1) :
    |2*a*(2-a)*(p-m)*t| ≤ δ := by
  obtain ⟨haN0, haN1⟩ := shortening_bounds ha ha1
  have he := mul_le_mul hp ht (abs_nonneg t) (by linarith : 0 ≤ δ/2)
  have hm := mul_le_mul haN1 he (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num : (0:ℝ) ≤ 1)
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha,
    abs_of_nonneg (show 0 ≤ 2-a by linarith)]
  norm_num
  nlinarith only [hm]

lemma midpoint_transverse_error {a p m t δ : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hδ : 0 ≤ δ) (hp : |p-m| ≤ δ/2) (ht : |t| ≤ 1) :
    ‖(a*(2-a)*(p-m)^2*t) • transverse‖ ≤ δ^2 := by
  obtain ⟨haN0, haN1⟩ := shortening_bounds ha ha1
  have he : (p-m)^2 ≤ δ^2/4 := by
    have h := mul_le_mul hp hp (abs_nonneg _) (div_nonneg hδ (by norm_num))
    rw [← sq, sq_abs] at h
    nlinarith only [h]
  have h1 := mul_le_mul haN1 he (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have h2 := mul_le_mul h1 ht (abs_nonneg t) (by positivity)
  have h3 := mul_le_mul h2 transverse_norm_le (norm_nonneg transverse) (by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg haN0,
    abs_of_nonneg (sq_nonneg _)]
  nlinarith only [h3, sq_nonneg δ]

theorem intercept_mem_paddedSector {a l r δ p h t : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/2) (hδ : 0 ≤ δ) (hlen : r-l = δ)
    (hp : p ∈ Icc l r) (hh : h ∈ Icc (0:ℝ) (2-a)) (ht : |t| ≤ 1) :
    intercept a p ((l+r)/2) h t ∈ paddedSector a l r δ := by
  have hmid : |p-(l+r)/2| ≤ δ/2 := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hr := midpoint_radial_error ha ha1 hδ hmid ht
  have he := midpoint_transverse_error ha ha1 hδ hmid ht
  let d := h-2*a*(2-a)*(p-(l+r)/2)*t
  have hd : d ∈ Icc (-δ) (2-a+δ) := by
    dsimp [d]
    constructor <;> linarith [hh.1, hh.2, (abs_le.mp hr).1, (abs_le.mp hr).2]
  apply Metric.mem_cthickening_of_dist_le _ (d • radial p) (δ^2) (sector a l r δ)
  · exact ⟨p, hp, d, hd, rfl⟩
  · rw [dist_eq_norm, intercept_decomposition]
    simpa only [d, add_sub_cancel_left] using he

theorem sector_isCompact (a l r δ : ℝ) : IsCompact (sector a l r δ) := by
  have heq : sector a l r δ =
      (fun z : ℝ × ℝ => z.2 • radial z.1) '' (Icc l r ×ˢ Icc (-δ) (2-a+δ)) := by
    ext z
    constructor
    · rintro ⟨p, hp, d, hd, rfl⟩
      exact ⟨(p,d), ⟨hp,hd⟩, rfl⟩
    · rintro ⟨⟨p,d⟩, ⟨hp,hd⟩, rfl⟩
      exact ⟨p,hp,d,hd,rfl⟩
  rw [heq]
  apply (isCompact_Icc.prod isCompact_Icc).image
  unfold radial
  fun_prop

theorem paddedSector_isCompact (a l r δ : ℝ) : IsCompact (paddedSector a l r δ) :=
  (sector_isCompact a l r δ).cthickening

theorem paddedSector_measurable (a l r δ : ℝ) : MeasurableSet (paddedSector a l r δ) :=
  (paddedSector_isCompact a l r δ).measurableSet

theorem paddedSector_finiteMeasure (a l r δ : ℝ) :
    MeasureTheory.volume (paddedSector a l r δ) < ⊤ :=
  (paddedSector_isCompact a l r δ).measure_lt_top

end CylinderCovering.BeamNeighborhood

end

end OAI
