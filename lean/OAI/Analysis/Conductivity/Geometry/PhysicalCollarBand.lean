import Mathlib
import OAI.Analysis.Conductivity.Branching.CollarMeasureTransport
import OAI.Analysis.Conductivity.Fourier.CollarAngularInverse
import OAI.Analysis.Conductivity.Flux.CollarCartesianDifferential

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma squareFace_scaled_surjective (v : Fin 2 → ℝ) {r : ℝ} (hr : 0<r)
    (hv : max |v 0| |v 1|=r) :
    ∃ i : Fin 4, ∃ a : ℝ, |a|≤1 ∧ v=r • squareFace i a := by
  have hs : max |(r⁻¹ • v) 0| |(r⁻¹ • v) 1|=1 := by
    simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [←mul_max_of_nonneg _ _ (inv_nonneg.mpr hr.le),hv,inv_mul_cancel₀ hr.ne']
  obtain ⟨i,a,ha,he⟩ := squareFace_min_max (r⁻¹ • v) hs
  refine ⟨i,a,ha,?_⟩
  rw [he,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]

def sourceClosedCollarBand (l r : ℝ) : Set (Fin 3 → ℝ) :=
  sourceCollarTime ⁻¹' Icc l r

lemma sourceRadial_pos_of_time {y : Fin 3 → ℝ}
    (ht : -(1:ℝ)/100 ≤ sourceCollarTime y) : 0<sourceRadial y := by
  have hm : |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth|≤1+(1:ℝ)/100 := by
    have h := le_max_left |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2|
    change -(1:ℝ)/100≤1-max |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth| |y 2| at ht
    linarith
  have hn := (abs_le.mp hm).1
  norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole] at hn
  linarith

lemma sourceCollarPiece_cover_extended {y : Fin 3 → ℝ}
    (hr : 0<sourceRadial y) (ht : sourceCollarTime y<1) :
    ∃ i j : Fin 4, ∃ a b : ℝ, |a|≤1 ∧ |b|≤1 ∧
      sourceCollarPiece i j ![sourceCollarTime y,a,b]=y := by
  have hL : 0<sourceLength := by norm_num [sourceLength]
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hq : 0<1-sourceCollarTime y := sub_pos.mpr ht
  have havg : max |![y 0/sourceLength,y 1] 0| |![y 0/sourceLength,y 1] 1|=sourceRadial y := by
    simp [sourceRadial,abs_div,abs_of_pos hL]
  obtain ⟨i,a,ha,he⟩ := squareFace_scaled_surjective ![y 0/sourceLength,y 1] hr havg
  have hcross : max |sourceCrossCoordinates y 0| |sourceCrossCoordinates y 1|=1-sourceCollarTime y := by
    simp [sourceCollarTime]
  obtain ⟨j,b,hb,hb'⟩ := squareFace_scaled_surjective (sourceCrossCoordinates y) hq hcross
  have hrad : sourceCollarRadius j (sourceCollarTime y) b=sourceRadial y := by
    have hh := congrFun hb' 0
    change (sourceRadial y-sourceRadialCenter)/sourceRadialWidth=
      (1-sourceCollarTime y)*squareFace j b 0 at hh
    have hh' := (div_eq_iff hw.ne').mp hh
    dsimp [sourceCollarRadius]
    nlinarith [hh']
  refine ⟨i,j,a,b,ha,hb,?_⟩
  ext k
  fin_cases k
  · have hx := congrFun he 0
    change y 0/sourceLength=sourceRadial y*squareFace i a 0 at hx
    change sourceLength*sourceCollarRadius j (sourceCollarTime y) b*squareFace i a 0=y 0
    rw [hrad]
    have hh := (div_eq_iff hL.ne').mp hx
    nlinarith
  · have hx := congrFun he 1
    change y 1=sourceRadial y*squareFace i a 1 at hx
    change sourceCollarRadius j (sourceCollarTime y) b*squareFace i a 1=y 1
    rw [hrad]; exact hx.symm
  · have hx := congrFun hb' 1
    change y 2=(1-sourceCollarTime y)*squareFace j b 1 at hx
    exact hx.symm

lemma sourcePhysicalCoordinates_right {y : Fin 3 → ℝ}
    (ht : sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100)) :
    sourceAngularCollar (sourceCollarTime y) (sourcePhysicalAngles y)=y := by
  obtain ⟨i,j,a,b,ha,hb,he⟩ := sourceCollarPiece_cover_extended
    (sourceRadial_pos_of_time ht.1) (by linarith [ht.2])
  have he' : sourceAngularCollar (sourceCollarTime y)
      (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))=y :=
    (sourceFaceAngles_physical i j ha hb).trans he
  have hinv := sourcePhysicalAngles_angular ht
    (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))
  rw [he'] at hinv
  rw [hinv]
  exact he'

lemma sourceClosedCollarBand_eq (l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    sourceClosedCollarBand l r=
      ⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r := by
  ext y
  constructor
  · intro hy
    obtain ⟨i,j,a,b,ha,hb,he⟩ := sourceCollarPiece_cover_extended
      (sourceRadial_pos_of_time (hl.trans hy.1)) (by linarith [hy.2])
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,
      ⟨![sourceCollarTime y,a,b],mem_sourceExtendedBox.mpr ⟨hy,ha,hb⟩,he⟩⟩⟩
  · intro hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hy
    obtain ⟨j,x,hx,rfl⟩ := mem_iUnion.mp hi
    obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
    have hb' := sourceFaceAngles_physical i j ha hb
    rw [←hb']
    change sourceCollarTime (sourceAngularCollar (x 0) _)∈Icc l r
    rw [sourceAngular_time ⟨hl.trans ht.1,ht.2.trans hr⟩]
    exact ht

lemma isCompact_sourceClosedCollarBand {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) : IsCompact (sourceClosedCollarBand l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  apply isCompact_iUnion
  intro i
  apply isCompact_iUnion
  intro j
  exact isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous

lemma sourceDirection_ne_zero_of_time {y : Fin 3 → ℝ}
    (ht : sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100)) (j : Fin 2) :
    sourceComplexDirections y j≠0 := by
  rw [←sourcePhysicalCoordinates_right ht,sourceComplexDirections_angular ht]
  fin_cases j
  · apply mul_ne_zero
    · apply Complex.ofReal_ne_zero.mpr
      exact (div_pos (sourceAngular_radius_pos ht _)
        (lt_of_lt_of_le (by norm_num) (rayDenominator_lower (by norm_num) (by norm_num) _))).ne'
    · exact Circle.coe_ne_zero _
  · apply mul_ne_zero
    · apply Complex.ofReal_ne_zero.mpr
      exact (div_pos (by linarith [ht.2])
        (lt_of_lt_of_le (by norm_num) (rayDenominator_lower
          (by norm_num [sourceRadialWidth,sourceHole])
          (by norm_num [sourceRadialWidth,sourceHole]) _))).ne'
    · exact Circle.coe_ne_zero _

lemma sourceClosedCollarBand_measure_le {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r) ≤ sourcePhysicalCollarMeasure l r := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  calc
    _ ≤ Measure.sum (fun i : Fin 4 => volume.restrict
        (⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)) := Measure.restrict_iUnion_le
    _ = ∑ i : Fin 4,volume.restrict
        (⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r) := Measure.sum_fintype _
    _ ≤ ∑ i : Fin 4,∑ j : Fin 4,volume.restrict
        (sourceCollarPiece i j '' sourceExtendedBox l r) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Measure.sum_fintype] using
        (Measure.restrict_iUnion_le (μ:=volume)
          (s:=fun j : Fin 4 => sourceCollarPiece i j '' sourceExtendedBox l r))
    _ = _ := rfl

lemma sourceClosedCollarBand_memLp {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {f : (Fin 3 → ℝ) → ℂ}
    (hf : MemLp f 2 (sourcePhysicalCollarMeasure l r)) :
    MemLp f 2 (volume.restrict (sourceClosedCollarBand l r)) :=
  hf.mono_measure (sourceClosedCollarBand_measure_le hl hr)

end ScalarConductivity

end

end OAI
