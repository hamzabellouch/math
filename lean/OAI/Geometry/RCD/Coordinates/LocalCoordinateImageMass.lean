import OAI.Geometry.RCD.Coordinates.CoordinateImageMass

namespace OAI

/-! # Localizing image mass to its actual source preimage -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem local_source_mass_of_image_defect {n : ℕ}
    (hEuclidean : hausdorff n (Euclidean n) = volume)
    {v : X → Euclidean n} {U S : Set X} {C : ℝ≥0}
    (hU : IsCompact U) (hv : LipschitzOnWith C v U) (hfin : hausdorff n X S ≠ ⊤)
    (z : Euclidean n) (R δ : ℝ)
    (hpreimage : ∀ x ∈ U, v x ∈ ball z R → x ∈ S)
    (hdefect : volume.real (ball z R \ v '' U) ≤ δ*volume.real (ball z R)) :
    (1-δ)*volume.real (ball z R) ≤ (C:ℝ)^n*(hausdorff n X).real S := by
  have himage : IsCompact (v '' U) := hU.image_of_continuousOn hv.continuousOn
  have hsplit := measureReal_inter_add_sdiff (μ := (volume : Measure (Euclidean n)))
    himage.measurableSet (s := ball z R) measure_ball_ne_top
  have hcap : hausdorff n X (U ∩ S) ≠ ⊤ := measure_ne_top_of_subset inter_subset_right hfin
  have hv' := hv.mono (inter_subset_left : U ∩ S ⊆ U)
  have htargetfin : hausdorff n (Euclidean n) (v '' (U ∩ S)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hcap)
      (normalized_hausdorff_image_le hv')
  have hsub : ball z R ∩ v '' U ⊆ v '' (U ∩ S) := by
    rintro y ⟨hy,x,hx,rfl⟩
    exact ⟨x,⟨hx,hpreimage x hx hy⟩,rfl⟩
  have hinter := measureReal_mono hsub (show volume (v '' (U ∩ S)) ≠ ⊤ by
    rwa [hEuclidean] at htargetfin)
  have hmass := normalized_hausdorff_real_image_le hv' hcap
  rw [hEuclidean] at hmass
  have hcapmass : (hausdorff n X).real (U ∩ S) ≤ (hausdorff n X).real S :=
    measureReal_mono inter_subset_right hfin
  have hbound := mul_le_mul_of_nonneg_left hcapmass (pow_nonneg C.coe_nonneg n)
  nlinarith only [hsplit,hdefect,hinter,hmass,hbound]

theorem local_source_mass_of_image_error {n : ℕ}
    (hEuclidean : hausdorff n (Euclidean n) = volume)
    {v : X → Euclidean n} {U S : Set X} {C : ℝ≥0}
    (hU : IsCompact U) (hv : LipschitzOnWith C v U) (hfin : hausdorff n X S ≠ ⊤)
    (z : Euclidean n) {R : ℝ} (hR : 0 < R) (E : ℝ)
    (hpreimage : ∀ x ∈ U, v x ∈ ball z R → x ∈ S)
    (herror : volume.real (ball z R \ v '' U) ≤ E) :
    volume.real (ball z R)-E ≤ (C:ℝ)^n*(hausdorff n X).real S := by
  have hpos : 0 < volume.real (ball z R) := ENNReal.toReal_pos
    (measure_ball_pos volume z hR).ne' measure_ball_ne_top
  have hh := local_source_mass_of_image_defect hEuclidean hU hv hfin z R
    (E/volume.real (ball z R)) hpreimage (by
      rwa [div_mul_cancel₀ E hpos.ne'])
  have he : (1-E/volume.real (ball z R))*volume.real (ball z R)=
      volume.real (ball z R)-E := by field_simp
  rwa [he] at hh

end RegularPointCoordinates

end

end OAI
