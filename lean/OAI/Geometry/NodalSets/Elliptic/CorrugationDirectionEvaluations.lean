import OAI.Geometry.NodalSets.Elliptic.CorrugationLeadingLength

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationLeadingVector_second_orthogonal (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) :
    g (corrugationLeadingVector amp t e z) (e (Pi.single 1 1)) = 0 := by
  simp [corrugationLeadingVector,corrugationFastVector,map_add,map_smul,he,Fin.ext_iff]

lemma corrugationLeadingVector_angular_orthogonal (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) (hr : corrugationCellRadius z ≠ 0) :
    g (corrugationLeadingVector amp t e z)
      (frozenPlaneVector e (-((corrugationCellPoint z).2/corrugationCellRadius z))
        ((corrugationCellPoint z).1/corrugationCellRadius z)) = 0 := by
  have hrot := frozenPlaneVector_rotating_frame g e he (corrugation_cell_unit_coefficients z hr)
  have haxis := frozenPlaneVector_axis_pair g e he
    (-((corrugationCellPoint z).2/corrugationCellRadius z))
    ((corrugationCellPoint z).1/corrugationCellRadius z) 0 (by decide)
  simp only [corrugationLeadingVector,corrugationFastVector_radial amp e z hr,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul,haxis.1,hrot.2.2.1]
  ring

lemma corrugation_normalized_leading_radial_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    {amp t : ℝ} (ha : 0 ≤ amp) (ht : 0 ≤ t) (z : ℝ × ℝ)
    (hr : corrugationCellRadius z ≠ 0) :
    |g (frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
      ((corrugationCellPoint z).2/corrugationCellRadius z))
      (metricNormalize g (corrugationLeadingVector amp t e z))| ≤
      t*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
  let r := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  have hrr : g r r = 1 := (frozenPlaneVector_rotating_frame g e he
    (corrugation_cell_unit_coefficients z hr)).1
  have haxis : g r (e (Pi.single 0 1)) = 0 :=
    (frozenPlaneVector_axis_pair g e he _ _ 0 (by decide)).2
  have hpair : g r (corrugationLeadingVector amp t e z) =
      t*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
    rw [corrugationLeadingVector,corrugationFastVector_radial amp e z hr]
    change g r (e (Pi.single 0 1)+t • (corrugationSlope amp (1/4) (corrugationCellRadius z) • r)) = _
    simp [map_add,map_smul,haxis,hrr]
  have hlen := corrugationLeadingVector_length_ge_one g e he amp t z
  have hsqrt : 1 ≤ Real.sqrt (g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z)) :=
    (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hlen)
  have hi : (Real.sqrt (g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z)))⁻¹ ≤ 1 :=
    by simpa using inv_anti₀ zero_lt_one hsqrt
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha (corrugationCellRadius_properties z).1
  change |g r (metricNormalize g (corrugationLeadingVector amp t e z))| ≤ _
  rw [metricNormalize,map_smul,smul_eq_mul,hpair,abs_of_nonneg (by positivity)]
  nlinarith [mul_nonneg ht hl]

lemma frozen_pairing_error (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (r v w : Coord)
    {M K δ : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hr : ‖r‖ ≤ K) (hd : ‖v-w‖ ≤ δ) :
    |g r v-g r w| ≤ M*K*δ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hd
  calc
    _ = |g r (v-w)| := by rw [map_sub]
    _ ≤ ‖g‖*‖r‖*‖v-w‖ := bilinear_pairing_bound _ _ _
    _ ≤ M*K*δ := by gcongr

lemma radial_angular_transfer (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (r t v : Coord)
    {M K δ : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hg : ‖g‖ ≤ M) (hr : ‖r‖ ≤ K) (ht : ‖t‖ ≤ K)
    (hrt : g r t = 0) (htt : g t t = 1) (hd : ‖v-t‖ ≤ δ)
    (hsmall : M*K*δ ≤ 1/2) :
    |g r v| ≤ M*K*δ ∧ 1/2 ≤ g t v := by
  have h1 := frozen_pairing_error g r v t hM hK hg hr hd
  have h2 := frozen_pairing_error g t v t hM hK hg ht hd
  rw [hrt,sub_zero] at h1
  rw [htt] at h2
  refine ⟨h1,?_⟩
  have hh := (abs_le.mp h2).1
  linarith

end
end Yau.Geometry

end OAI
