import OAI.Geometry.CylinderCovering.Beams.FullDefinitions
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodFinite
import OAI.Geometry.CylinderCovering.Convexity.AmbientCylinderBridge

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ShortenedBeam
open CylinderCovering

lemma doubleSector_eq_sector (a : ℝ) (N : ℕ) (i : Fin N) :
    doubleSector a N i = BeamNeighborhood.sector a
      (RadialRiemann.point 0 1 N i) (RadialRiemann.point 0 1 N (i+1))
      (RadialRiemann.step 0 1 N) := by
  have hv (r p : ℝ) : (!₂[r*p,r*(1-p)] : ParameterPlane) =
      r • BeamNeighborhood.radial p := by
    ext j
    fin_cases j <;> simp [BeamNeighborhood.radial]
  simp only [doubleSector, BeamNeighborhood.sector, RadialRiemann.cell,
    RadialRiemann.step, sub_zero, hv]

lemma neighborhoodSector_eq_paddedSector (a : ℝ) (N : ℕ) (i : Fin N) :
    neighborhoodSector a N i = BeamNeighborhood.paddedSector a
      (RadialRiemann.point 0 1 N i) (RadialRiemann.point 0 1 N (i+1))
      (RadialRiemann.step 0 1 N) := by
  rw [neighborhoodSector, doubleSector_eq_sector]
  simp only [BeamNeighborhood.paddedSector, RadialRiemann.step, sub_zero]

lemma neighborhoodBaseMinus_eq_beamBaseMinus (a : ℝ) (N : ℕ) (i : Fin N) :
    neighborhoodBaseMinus a N i = BeamNeighborhoodRealization.beamBaseMinus a N i := by
  unfold neighborhoodBaseMinus BeamNeighborhoodRealization.beamBaseMinus
  rw [neighborhoodSector_eq_paddedSector]
  rfl

lemma neighborhoodBasePlus_eq_beamBasePlus (a : ℝ) (N : ℕ) (i : Fin N) :
    neighborhoodBasePlus a N i = BeamNeighborhoodRealization.beamBasePlus a N i := by
  unfold neighborhoodBasePlus BeamNeighborhoodRealization.beamBasePlus
  rw [neighborhoodSector_eq_paddedSector]
  rfl

theorem neighborhoodAlternativeStatement : NeighborhoodAlternativeStatement := by
  intro a ha ha1
  obtain ⟨E,hE,h⟩ := BeamNeighborhoodRealization.alternativeStatement a ha ha1
  let Cm : (N : ℕ) → Fin N → RuledApproximation.Cylinder := fun N i =>
    RuledApproximation.Cylinder.fromAmbientBase
      (axisMinus a (BeamNeighborhoodRealization.cellMidpoint N i))
      (((h N (Nat.zero_lt_of_lt i.isLt)).1 i).1)
      (BeamNeighborhoodRealization.beamBaseMinus a N i)
  let Cp : (N : ℕ) → Fin N → RuledApproximation.Cylinder := fun N i =>
    RuledApproximation.Cylinder.fromAmbientBase
      (axisPlus a (BeamNeighborhoodRealization.cellMidpoint N i))
      (((h N (Nat.zero_lt_of_lt i.isLt)).1 i).2.1)
      (BeamNeighborhoodRealization.beamBasePlus a N i)
  have hs : 0 < Real.sqrt (2:ℝ)/4 := by positivity
  refine ⟨E/(Real.sqrt 2/4), (div_pos hE hs).le, Cm, Cp, ?_⟩
  intro N hN
  obtain ⟨hbase,hminus,hplus,hcost⟩ := h N hN
  have hpminus (i : Fin N) : ∀ z ∈ BeamNeighborhoodRealization.beamBaseMinus a N i,
      inner ℝ (axisMinus a (BeamNeighborhoodRealization.cellMidpoint N i)) z = 0 :=
    (hbase i).2.2.2.2.2.2.2.2.1
  have hpplus (i : Fin N) : ∀ z ∈ BeamNeighborhoodRealization.beamBasePlus a N i,
      inner ℝ (axisPlus a (BeamNeighborhoodRealization.cellMidpoint N i)) z = 0 :=
    (hbase i).2.2.2.2.2.2.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    refine ⟨rfl,rfl,?_,?_,?_,?_⟩
    · rw [neighborhoodBaseMinus_eq_beamBaseMinus]
      exact RuledApproximation.Cylinder.fromAmbientBase_image _ _ _ (hpminus i)
    · rw [neighborhoodBasePlus_eq_beamBasePlus]
      exact RuledApproximation.Cylinder.fromAmbientBase_image _ _ _ (hpplus i)
    · exact RuledApproximation.Cylinder.fromAmbientBase_compact _ _ _
        (hpminus i) (hbase i).2.2.1
    · exact RuledApproximation.Cylinder.fromAmbientBase_compact _ _ _
        (hpplus i) (hbase i).2.2.2.1
  · intro z hz
    obtain ⟨i,hi⟩ := hminus z hz
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    change z ∈ (RuledApproximation.Cylinder.fromAmbientBase _ _ _).carrier
    rw [RuledApproximation.Cylinder.fromAmbientBase_carrier _ _ _ (hpminus i)]
    exact hi
  · intro z hz
    obtain ⟨i,hi⟩ := hplus z hz
    apply mem_iUnion.mpr
    refine ⟨i,?_⟩
    change z ∈ (RuledApproximation.Cylinder.fromAmbientBase _ _ _).carrier
    rw [RuledApproximation.Cylinder.fromAmbientBase_carrier _ _ _ (hpplus i)]
    exact hi
  · have harea : RuledApproximation.familyArea (Cm N) +
        RuledApproximation.familyArea (Cp N) =
        BeamNeighborhoodRealization.alternativeCost a N := by
      unfold RuledApproximation.familyArea BeamNeighborhoodRealization.alternativeCost
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        exact RuledApproximation.Cylinder.fromAmbientBase_area _ _ _ (hpminus i)
      · apply Finset.sum_congr rfl
        intro i _
        exact RuledApproximation.Cylinder.fromAmbientBase_area _ _ _ (hpplus i)
    rw [harea]
    apply (div_le_iff₀ hs).mpr
    have hunit : Real.sqrt (2:ℝ) ≠ 0 := by positivity
    have hn : (N:ℝ) ≠ 0 := by positivity
    convert hcost using 1
    first | rfl | field_simp [hunit, hn]

end ShortenedBeam

end

end OAI
