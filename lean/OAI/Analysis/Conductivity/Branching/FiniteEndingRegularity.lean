import Mathlib
import OAI.Analysis.Conductivity.Branching.Ending
import OAI.Analysis.Conductivity.Branching.CascadeRankPieces
import OAI.Analysis.Conductivity.Geometry.RegularPatchTranslation

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def finiteEndingSymmetricTensor (a J L K : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨finiteEndingTensor a J L K x,finiteEndingTensor_symm a J L K x⟩

lemma finiteEnding_initial_regular (a J L K : ℝ) (x : Coord3)
    (ht : x 0<J+2) (hsin : sin (x 1)≠0)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (finiteEndingValue a J L K)) (finiteEndingSymmetricTensor a J L K) U := by
  let F := pureModeValue (initialConnectorProfile a (1/2) J) 1
  let B : Coord3 → Symmetric3 := fun y =>
    ⟨pureModeTensor (initialConnectorAngular a (1/2) J (y 0)) 1,pureModeTensor_symm _ _⟩
  have hF := pureModeValue_smooth (initialConnectorProfile_smooth a (1/2) J) (1:Fin 3)
  have hB : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => (B y).val) := by
    apply pureModeTensor_smooth
    exact (initialConnectorAngular_smooth a (1/2) J).comp (contDiff_apply ℝ ℝ 0)
  apply axialPair_mem_regularRegion_of_model hF hB (i:=1) ?_ ?_ (by decide) ?_ hU hx
  · exact axial_paste_eventually_left (continuous_apply 0) ht
  · filter_upwards [(isOpen_lt (continuous_apply (0:Fin 3)) continuous_const).mem_nhds ht] with y hy
    apply Subtype.ext
    exact ite_eq_left hy
  · rw [pureModeValue_direction ((initialConnectorProfile_smooth a (1/2) J).differentiable (by simp))]
    norm_num only [show (1:Fin 3)≠0 from by decide,ite_false,ite_true,zero_add]
    exact mul_ne_zero (neg_ne_zero.mpr (initialConnectorProfile_pos _ _ _ _).ne') hsin

lemma finiteEnding_cascade_regular {a J L K : ℝ} (x : Coord3) (ht : J+2<x 0)
    (hr : x-Pi.single 0 (J+2)∈regularRegion
      (axialPair (cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2))))
      (cascadeSymmetricTensor L K 1) univ)
    {U : Set Coord3} (hU : IsOpen U) (hx : x∈U) :
    x∈regularRegion (axialPair (finiteEndingValue a J L K)) (finiteEndingSymmetricTensor a J L K) U := by
  have htrans := mem_regularRegion_translate hr (![J+2,0])
  apply mem_regularRegion_congr_nhds htrans ?_ ?_ hU hx
  · have he : finiteEndingValue a J L K =ᶠ[𝓝 x]
        fun y => cascadeValue L K 1 (initialConnectorProfile a (1/2) J (J+2)) (y-Pi.single 0 (J+2)) :=
      axial_paste_eventually_right (continuous_apply 0) ht
    filter_upwards [he] with y hy
    rw [show (![J+2,0] : Fin 2 → ℝ)=![(Pi.single 0 (J+2) : Coord3) 0,0] by simp,
      axialPair_translate]
    simp only [axialPair,hy]
  · filter_upwards [(isOpen_lt continuous_const (continuous_apply (0:Fin 3))).mem_nhds ht] with y hy
    apply Subtype.ext
    exact ite_eq_right (not_lt.mpr hy.le)

theorem finiteEnding_regularRegion_ae {a J L K : ℝ} (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U →
      x∈regularRegion (axialPair (finiteEndingValue a J L K)) (finiteEndingSymmetricTensor a J L K) U := by
  have he := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 (J+2))).quasiMeasurePreserving.ae
    (cascade_regularRegion_ae hL hK (by norm_num : (1:ℝ)≠0)
      (initialConnectorProfile_pos a (1/2) J (J+2)).ne' isOpen_univ)
  simp only [←sub_eq_add_neg] at he
  have hsin : ∀ᵐ x : Coord3,sin (x 1)≠0 := by
    simpa only [one_mul] using ae_sin_coord_ne_zero (by norm_num : (1:ℝ)≠0) (1:Fin 3)
  filter_upwards [he,hsin,ae_coord3_ne 0 (J+2)] with x hr hxs hxt
  intro hx
  rcases lt_or_gt_of_ne hxt with hl|hh
  · exact finiteEnding_initial_regular a J L K x hl hxs hU hx
  · apply finiteEnding_cascade_regular x hh (hr (mem_univ _) ?_) hU hx
    simp only [one_mul,Pi.sub_apply,Pi.single_eq_same]
    linarith

lemma finiteEnding_regularRegion_conull {a J L K : ℝ} (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    volume (U \ regularRegion (axialPair (finiteEndingValue a J L K))
      (finiteEndingSymmetricTensor a J L K) U)=0 := by
  classical
  have hh := ae_iff.mp (finiteEnding_regularRegion_ae (a:=a) (J:=J) hL hK hU)
  convert hh using 2
  ext x
  simp only [Set.mem_sdiff, mem_ofPred_eq]
  tauto

end ScalarConductivity

end

end OAI
