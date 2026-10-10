import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.LocalFieldScalarBoundBarrier

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
attribute [local irreducible] formEnergy energy

 theorem unshifted_local_field_scale (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {D : ℝ} (hD : 0 ≤ D)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D)
    (y : Space) {a : ℝ} (ha : 0 < a) (hs : 12*a ≤ ‖y‖) :
    coreFieldSquare Z 0 y ψ ≤ localFieldUniversalConstant*
      localFieldScale a D (rawCountMoment ψ y (8*a)) := by
  have hh (lam : ℝ) (hlam : 0 < lam) :
      coreFieldSquare Z lam y ψ ≤ localFieldUniversalConstant*
        localFieldScale a (D+lam*N) (rawCountMoment ψ y (8*a)) := by
    have hf := ensemble_local_field_scale (CoreObservationEnsemble.initial ψ hψ)
      y ha hs (by simpa only [CoreObservationEnsemble.initial_mass] using hm) (Nat.cast_nonneg Z) hlam
    simp only [CoreObservationEnsemble.initial_fieldMoment,
      CoreObservationEnsemble.initial_excess,CoreObservationEnsemble.initial_countMoment] at hf
    have hex := unshifted_priced_excess_bound Z hm hlam he
    exact hf.trans (mul_le_mul_of_nonneg_left
      (localFieldScale_mono ha (max_le hex (by positivity)) le_rfl)
      localFieldUniversalConstant_pos.le)
  let eps (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hp (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have ht : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Continuous (fun t : ℝ => coreFieldSquare Z t y ψ) := by
    unfold coreFieldSquare normalizedCoreField
    fun_prop
  have hc' : Continuous (fun t : ℝ => localFieldUniversalConstant*
      localFieldScale a (D+t*N) (rawCountMoment ψ y (8*a))) := by
    unfold localFieldScale
    fun_prop
  have ht' : Tendsto (fun n => localFieldUniversalConstant*
      localFieldScale a (D+eps n*N) (rawCountMoment ψ y (8*a))) atTop
      (𝓝 (localFieldUniversalConstant*localFieldScale a D (rawCountMoment ψ y (8*a)))) := by
    simpa only [Function.comp_def,zero_mul,add_zero] using hc'.continuousAt.tendsto.comp ht
  exact le_of_tendsto_of_tendsto (hc.continuousAt.tendsto.comp ht) ht'
    (Eventually.of_forall (fun n => hh (eps n) (hp n)))

 theorem unshifted_enlarged_cell_count (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {D : ℝ} (hD : 0 ≤ D)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D)
    {y : Space} (hy : y ≠ 0) :
    rawCountMoment ψ y (32*localCellRadius y) ≤ actualCellMomentConstant*(localOffsetMass D y)^2 := by
  have hh := enlarged_cell_count_le hψ.sobolevVector hD hy
  have hp := unshifted_local_count_supremum Z hψ hm hD he
  have hC : 0 ≤ localCountCoverConstant := le_trans zero_le_one localCountCoverConstant_one_le
  unfold actualCellMomentConstant
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (sq_nonneg _))

 def unshiftedLocalFieldConstant : ℝ := localFieldUniversalConstant*(6+actualCellMomentConstant)
 lemma unshiftedLocalFieldConstant_pos : 0 < unshiftedLocalFieldConstant := by
  have := actualCellMomentConstant_one_le
  exact mul_pos localFieldUniversalConstant_pos (by linarith)

 theorem unshifted_local_field_normalized (Z : ℕ) {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {D : ℝ} (hD : 0 ≤ D)
    (he : formEnergy Z ψ ≤ sInf (Set.range (energy (Z:ℝ)))+D)
    {y : Space} (hy : y ≠ 0) :
    coreFieldSquare Z 0 y ψ ≤ unshiftedLocalFieldConstant*
      (localOffsetMass D y/localCellRadius y)^2 := by
  let a := localCellRadius y
  let m := localOffsetMass D y
  have ha : 0 < a := localCellRadius_pos hy
  have hsep : 12*a ≤ ‖y‖ := by dsimp [a,localCellRadius]; linarith [norm_nonneg y]
  have hb : rawCountMoment ψ y (8*a) ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y
      (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+8*a ≤ 32*a)).trans
        (unshifted_enlarged_cell_count Z hψ hm hD he hy)
  have hlin := localFieldScale_linear_bound ha (localOffsetMass_one_le D y)
    (localOffsetMass_cube_le D y) actualCellMomentConstant_one_le hb (D := D)
  have hD' : D/a ≤ (m/a)^2 := by
    have hh := div_le_div_of_nonneg_right (localOffsetMass_offset hD hy) (sq_nonneg a)
    calc _ = (D*a)/a^2 := by field_simp
         _ ≤ m^2/a^2 := hh
         _ = _ := by ring
  calc
    _ ≤ localFieldUniversalConstant*localFieldScale a D (rawCountMoment ψ y (8*a)) :=
      unshifted_local_field_scale Z hψ hm hD he y ha hsep
    _ ≤ localFieldUniversalConstant*((6+actualCellMomentConstant)*(m/a)^2) := by
      apply mul_le_mul_of_nonneg_left _ localFieldUniversalConstant_pos.le
      linarith only [hlin,hD']
    _ = _ := by unfold unshiftedLocalFieldConstant; ring

end CoulombAtom

end

end OAI
