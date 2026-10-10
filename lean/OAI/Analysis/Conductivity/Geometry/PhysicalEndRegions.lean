import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralPhysicalRegion

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def physicalEndRegion (i : Fin 3) : Set (Fin 3 → ℝ) :=
  Fin.cases (sourceClosedCollarBand 0 centralThickness)
    (fun k => (sourceChildHomeomorph (actualChildSign k)).symm ⁻¹'
      sourceClosedCollarBand (-centralThickness) 0) i

lemma physicalEndRegion_compact (i : Fin 3) : IsCompact (physicalEndRegion i) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact isCompact_sourceClosedCollarBand (by norm_num) (by norm_num [centralThickness])
  · exact (sourceChildHomeomorph (actualChildSign k)).symm.isCompact_preimage.mpr
      (isCompact_sourceClosedCollarBand (by norm_num [centralThickness]) (by norm_num))

lemma sourceSmallBand_bounds {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-centralThickness) 0) :
    |y 0|≤1602/1000 ∧ |y 1|≤1001/1000 ∧ |y 2|≤1002/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-centralThickness)).mp hy.1
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma physicalChildEnd_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈sourceClosedCollarBand (-centralThickness) 0) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceSmallBand_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0<sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

lemma physicalEndRegion_parent_child_disjoint (k : Fin 2) :
    Disjoint (physicalEndRegion 0) (physicalEndRegion k.succ) := by
  apply disjoint_left.mpr
  intro y hp hc
  have hh := physicalChildEnd_far_parent k hc
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rw [he] at hh
  change sourceCollarTime y∈Icc 0 centralThickness at hp
  norm_num [centralThickness] at hp hh
  linarith [hp.2]

lemma physicalEndRegion_children_disjoint :
    Disjoint (physicalEndRegion 1) (physicalEndRegion 2) := by
  apply disjoint_left.mpr
  intro y h₀ h₁
  have ha := (sourceSmallBand_bounds h₀).2.1
  have hb := (sourceSmallBand_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0<sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

lemma physicalEndRegion_pairwise_disjoint : Pairwise (fun i j => Disjoint (physicalEndRegion i) (physicalEndRegion j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | exact (hij rfl).elim | exact physicalEndRegion_parent_child_disjoint 0 |
    exact physicalEndRegion_parent_child_disjoint 1 |
    exact (physicalEndRegion_parent_child_disjoint 0).symm |
    exact (physicalEndRegion_parent_child_disjoint 1).symm |
    exact physicalEndRegion_children_disjoint | exact physicalEndRegion_children_disjoint.symm

end ScalarConductivity

end
end

end OAI
