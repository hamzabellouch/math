import OAI.Geometry.RCD.Coordinates.RegularEuclideanHausdorff
import OAI.Geometry.RCD.Coordinates.NormalizedHausdorffImage

namespace OAI

/-! # Converting a small omitted image volume into source mass -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem source_mass_of_image_defect {n : ℕ}
    (hEuclidean : hausdorff n (Euclidean n) = volume)
    {v : X → Euclidean n} {U : Set X} {C : ℝ≥0}
    (hU : IsCompact U) (hv : LipschitzOnWith C v U) (hfin : hausdorff n X U ≠ ⊤)
    (z : Euclidean n) (R δ : ℝ)
    (hdefect : volume.real (ball z R \ v '' U) ≤ δ*volume.real (ball z R)) :
    (1-δ)*volume.real (ball z R) ≤ (C:ℝ)^n*(hausdorff n X).real U := by
  have himage : IsCompact (v '' U) := hU.image_of_continuousOn hv.continuousOn
  have hsplit := measureReal_inter_add_sdiff (μ := (volume : Measure (Euclidean n)))
    himage.measurableSet (s := ball z R) measure_ball_ne_top
  have hinter : volume.real (ball z R ∩ v '' U) ≤ volume.real (v '' U) :=
    measureReal_mono inter_subset_right himage.measure_lt_top.ne
  have hmass := normalized_hausdorff_real_image_le hv hfin
  rw [hEuclidean] at hmass
  nlinarith only [hsplit,hdefect,hinter,hmass]

end RegularPointCoordinates

end

end OAI
