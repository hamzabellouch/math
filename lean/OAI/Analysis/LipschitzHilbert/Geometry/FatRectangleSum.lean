import OAI.Analysis.LipschitzHilbert.Estimates.PositiveAuxiliaryAverages
import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiSelectionCover

namespace OAI

/-! Square averages control overlap with targets of bounded eccentricity. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {ι κ : Type*} [Fintype κ]

theorem rectangleCount_on_carrier (R : ι → Rectangle) (s : Finset ι) (T : Rectangle) :
    (∫⁻ x in T.carrier, rectangleCount R s x) = ∑ j ∈ s, volume (T.carrier ∩ (R j).carrier) := by
  unfold rectangleCount
  rw [lintegral_finsetSum s (fun j _ => measurable_const.indicator (R j).measurableSet_carrier)]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_indicator (R j).measurableSet_carrier,lintegral_const,
    Measure.restrict_restrict (R j).measurableSet_carrier,Measure.restrict_apply_univ,one_mul,inter_comm]

theorem rectangleCount_dilate_le (R : ι → Rectangle) (s : Finset ι) (a : ℝ) (ha : 1 ≤ a) :
    rectangleCount R s ≤ rectangleCount (fun j => (R j).dilate a (by linarith)) s := by
  intro x
  apply Finset.sum_le_sum
  intro j _
  by_cases hx : x ∈ (R j).carrier
  · have hx' := (R j).carrier_subset_dilate a ha hx
    simp only [indicator_of_mem hx,indicator_of_mem hx',le_refl]
  · simp only [indicator_of_notMem hx]
    exact zero_le

theorem rectangle_in_centeredSquare (T : Rectangle) (x : Plane) (hx : x ∈ T.carrier) :
    planeCoordinates ⁻¹' T.carrier ⊆ centeredSquare (planeCoordinates.symm x) (2*T.long) := by
  intro z hz
  have hd : ‖planeCoordinates z-x‖ ≤ 2*T.long := by
    simpa only [dist_eq_norm] using T.dist_le_two_long hz hx
  have h0 : |z.1-(planeCoordinates.symm x).1| ≤ 2*T.long := by
    have h := PiLp.norm_apply_le (planeCoordinates z-x) (0 : Fin 2)
    have hc : |z.1-(planeCoordinates.symm x).1| ≤ ‖planeCoordinates z-x‖ := by
      simpa [Real.norm_eq_abs,PiLp.sub_apply,planeCoordinates_apply,planeCoordinates_symm_apply] using h
    exact hc.trans hd
  have h1 : |z.2-(planeCoordinates.symm x).2| ≤ 2*T.long := by
    have h := PiLp.norm_apply_le (planeCoordinates z-x) (1 : Fin 2)
    have hc : |z.2-(planeCoordinates.symm x).2| ≤ ‖planeCoordinates z-x‖ := by
      simpa [Real.norm_eq_abs,PiLp.sub_apply,planeCoordinates_apply,planeCoordinates_symm_apply] using h
    exact hc.trans hd
  change (z.1 ∈ Icc _ _) ∧ (z.2 ∈ Icc _ _)
  constructor <;> constructor <;> linarith [abs_le.mp h0,abs_le.mp h1]

theorem fat_intersection_sum_le_auxiliary (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (s : Finset ι) (T : Rectangle) (B : ℝ) (hB : 0 ≤ B)
    (hfat : T.long ≤ B*T.short) (a : ℝ) (ha : 1 ≤ a)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume (T.carrier ∩ (R j).carrier)) ≤
      ENNReal.ofReal (576*B) * volume T.carrier *
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a (by linarith)) s) x := by
  let g := rectangleCount (fun j => (R j).dilate a (by linarith)) s
  let c := planeCoordinates.symm x
  let r := 2*T.long
  have hr : 0 < r := mul_pos (by norm_num) T.long_pos
  have hsub := rectangle_in_centeredSquare T x hx
  have hmass : (∫⁻ y in T.carrier, g y) =
      ∫⁻ z in planeCoordinates ⁻¹' T.carrier, g (planeCoordinates z) ∂volume.prod volume :=
    (planeCoordinates_measurePreserving.setLIntegral_comp_preimage T.measurableSet_carrier
      (rectangleCount_measurable _ _)).symm
  have hcenter : planeCoordinates.symm x ∈ centeredSquare c r := by
    change (c.1 ∈ Icc (c.1-r) (c.1+r)) ∧ (c.2 ∈ Icc (c.2-r) (c.2+r))
    constructor <;> constructor <;> linarith
  have haux := positiveAuxiliary_square_integral e g c r hr x hcenter
  have hcoef : (36:ℝ≥0∞)*(volume.prod volume) (centeredSquare c r) ≤
      ENNReal.ofReal (576*B)*volume T.carrier := by
    rw [centeredSquare_volume,Rectangle.volume_carrier]
    have he : (36:ℝ≥0∞)* (ENNReal.ofReal (2*r)*ENNReal.ofReal (2*r)) =
        ENNReal.ofReal (576*T.long^2) := by
      have hr0 : 0 ≤ 2*r := by positivity
      rw [←ENNReal.ofReal_mul hr0,show (36:ℝ≥0∞)=ENNReal.ofReal 36 by norm_num,
        ←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [r]
      ring
    rw [he,←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0 ≤ 576*B),
      ←ENNReal.ofReal_mul (mul_nonneg (by positivity : 0 ≤ 576*B) T.long_pos.le)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left hfat T.long_pos.le
    nlinarith
  calc
    _ = ∫⁻ y in T.carrier, rectangleCount R s y := (rectangleCount_on_carrier R s T).symm
    _ ≤ ∫⁻ y in T.carrier, g y := lintegral_mono (rectangleCount_dilate_le R s a ha)
    _ = _ := hmass
    _ ≤ ∫⁻ z in centeredSquare c r, g (planeCoordinates z) ∂volume.prod volume := lintegral_mono_set hsub
    _ ≤ 36*(volume.prod volume) (centeredSquare c r)*positiveAuxiliary e g x := haux
    _ ≤ _ := mul_le_mul' hcoef le_rfl

theorem fat_selected_overlap_bound (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (s previous : Finset ι) (hs : s ⊆ previous) (r : ι)
    (B : ℝ) (hB : 0 ≤ B) (hfat : (R r).long ≤ B*(R r).short)
    (a : ℝ) (ha : 1 ≤ a) (η : ℝ≥0∞) (hη : ENNReal.ofReal (576*B)*η ≤ 1)
    (hnot : ¬maximalBlocked e R a (by linarith) η previous r) :
    (∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier)) ≤ volume (R r).carrier := by
  classical
  let g := rectangleCount (fun j => (R j).dilate a (by linarith)) previous
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ η := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hlocal := fat_intersection_sum_le_auxiliary e R s (R r) B hB hfat a ha x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate a (by linarith)) hs) x
  calc
    _ ≤ ENNReal.ofReal (576*B)*volume (R r).carrier *
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a (by linarith)) s) x := hlocal
    _ ≤ ENNReal.ofReal (576*B)*volume (R r).carrier*η := mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal (576*B)*η)*volume (R r).carrier := by ring
    _ ≤ 1*volume (R r).carrier := mul_le_mul' hη le_rfl
    _ = _ := one_mul _

end LipschitzHilbert

end

end OAI
