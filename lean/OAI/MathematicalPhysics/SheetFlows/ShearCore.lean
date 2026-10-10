import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Localization

namespace OAI

/-! SheetFlows shear core. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

variable (d : Collar)

def coreLift0 : StationaryPulse :=
  StationaryPulse.tensor 2 ![Dprofile (1/2) d.size 5, Cprofile (1/2) d.size 6, fun _ => 1]
    (by intro k; fin_cases k
        · exact Dprofile_contDiff _ _ d.positive
        · exact Cprofile_contDiff _ _ d.positive
        · exact contDiff_const)
    (by intro k; fin_cases k
        · exact Dprofile_periodic _ _ _
        · exact Cprofile_periodic _ _ _
        · exact fun _ => rfl)
    (fun _ => rfl) 0
    (by apply Dprofile_integral_zero d.positive <;> linarith [d.small])

def coreLift1 : StationaryPulse :=
  StationaryPulse.tensor 2 ![Cprofile (1/2) d.size 5, Dprofile (1/2) d.size 6, fun _ => 1]
    (by intro k; fin_cases k
        · exact Cprofile_contDiff _ _ d.positive
        · exact Dprofile_contDiff _ _ d.positive
        · exact contDiff_const)
    (by intro k; fin_cases k
        · exact Cprofile_periodic _ _ _
        · exact Dprofile_periodic _ _ _
        · exact fun _ => rfl)
    (fun _ => rfl) 1
    (by apply Dprofile_integral_zero d.positive <;> linarith [d.small])

def coreHorizontal (j : Fin 2) : StationaryPulse :=
  StationaryPulse.tensor j.castSucc ![fun _ => 1, fun _ => 1, Dprofile (1/2) d.size 5]
    (by intro k; fin_cases k
        · exact contDiff_const
        · exact contDiff_const
        · exact Dprofile_contDiff _ _ d.positive)
    (by intro k; fin_cases k
        · exact fun _ => rfl
        · exact fun _ => rfl
        · exact Dprofile_periodic _ _ _)
    (by intro s; fin_cases j <;> rfl) 2
    (by apply Dprofile_integral_zero d.positive <;> linarith [d.small])

theorem coreLift0_field (x : Space) : (coreLift0 d).field x =
    (Dprofile (1/2) d.size 5 (x 0) * Cprofile (1/2) d.size 6 (x 1)) • basis 2 := by
  simp [coreLift0, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem coreLift1_field (x : Space) : (coreLift1 d).field x =
    (Cprofile (1/2) d.size 5 (x 0) * Dprofile (1/2) d.size 6 (x 1)) • basis 2 := by
  simp [coreLift1, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem coreHorizontal_field (j : Fin 2) (x : Space) : (coreHorizontal d j).field x =
    Dprofile (1/2) d.size 5 (x 2) • basis j.castSucc := by
  simp [coreHorizontal, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem coreC_one {c r : ℝ} (hc : c ∈ Set.Icc 5 6) (hr : |r| ≤ 1/2) :
    Cprofile (1/2) d.size c (c+r) = 1 := by
  apply Cprofile_one d.positive
  · linarith [d.small, hc.1]
  · linarith [d.small, hc.2]
  · have hh := abs_le.mp hr
    constructor <;> linarith [hc.1, hc.2, hh.1, hh.2]
  · rw [add_sub_cancel_left]
    linarith [d.positive]

theorem coreD_linear {c r : ℝ} (hc : c ∈ Set.Icc 5 6) (hr : |r| ≤ 1/2) :
    Dprofile (1/2) d.size c (c+r) = r := by
  have hl : 1/2 + d.size ≤ c := by linarith [d.small, hc.1]
  have hu : c + (1/2+d.size) ≤ 10 := by linarith [d.small, hc.2]
  have hp : c+r ∈ Set.Icc 0 10 := by
    have hh := abs_le.mp hr
    constructor <;> linarith [hc.1, hc.2, hh.1, hh.2]
  have hb : |c+r-c| ≤ 1/2+d.size/2 := by
    rw [add_sub_cancel_left]
    linarith [d.positive]
  simpa only [add_sub_cancel_left] using Dprofile_linear d.positive hl hu hp hb

theorem coreC_off {c y : ℝ} (hc : c ∈ Set.Icc 5 6) (hy : y ∈ Set.Icc 2 3) :
    Cprofile (1/2) d.size c y = 0 := by
  apply Cprofile_zero_on_chart d.positive
  · linarith [d.small, hc.1]
  · linarith [d.small, hc.2]
  · constructor <;> linarith [hy.1, hy.2]
  · apply le_abs.mpr (Or.inr ?_)
    linarith [d.small, hc.1, hy.2]

theorem coreD_off {c y : ℝ} (hc : c ∈ Set.Icc 5 6) (hy : y ∈ Set.Icc 2 3) :
    Dprofile (1/2) d.size c y = 0 := by
  apply Dprofile_zero_on_chart d.positive
  · linarith [d.small, hc.1]
  · linarith [d.small, hc.2]
  · constructor <;> linarith [hy.1, hy.2]
  · apply le_abs.mpr (Or.inr ?_)
    linarith [d.small, hc.1, hy.2]

theorem coreLift0_on {r s : ℝ} (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (z : ℝ) :
    (coreLift0 d).field ![5+r,6+s,z] = r • basis 2 := by
  simp only [coreLift0_field, Matrix.cons_val_zero, Matrix.cons_val_one,
    coreD_linear d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) hr,
    coreC_one d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hs, mul_one]

theorem coreLift1_on {r s : ℝ} (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (z : ℝ) :
    (coreLift1 d).field ![5+r,6+s,z] = s • basis 2 := by
  simp only [coreLift1_field, Matrix.cons_val_zero, Matrix.cons_val_one,
    coreC_one d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) hr,
    coreD_linear d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hs, one_mul]

theorem coreLift0_off (x : Space) (hx : x 1 ∈ Set.Icc 2 3) : (coreLift0 d).field x = 0 := by
  rw [coreLift0_field, coreC_off d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hx, mul_zero, zero_smul]

theorem coreLift1_off (x : Space) (hx : x 1 ∈ Set.Icc 2 3) : (coreLift1 d).field x = 0 := by
  rw [coreLift1_field, coreD_off d (by norm_num : (6:ℝ) ∈ Set.Icc 5 6) hx, mul_zero, zero_smul]

theorem coreHorizontal_on (j : Fin 2) (x y : ℝ) {r : ℝ} (hr : |r| ≤ 1/2) :
    (coreHorizontal d j).field ![x,y,5+r] = r • basis j.castSucc := by
  rw [coreHorizontal_field]
  change Dprofile (1/2) d.size 5 (5+r) • basis j.castSucc = _
  rw [coreD_linear d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) hr]

theorem coreHorizontal_off (j : Fin 2) (x : Space) (hx : x 2 = 2) :
    (coreHorizontal d j).field x = 0 := by
  rw [coreHorizontal_field, hx,
    coreD_off d (by norm_num : (5:ℝ) ∈ Set.Icc 5 6) (by norm_num : (2:ℝ) ∈ Set.Icc 2 3), zero_smul]

def tripleProgram0 (l : ℝ) : List StationaryPulse :=
  [coreLift0 d, (coreHorizontal d 0).scale (l-1), (coreLift0 d).scale (-1/l)]

def tripleProgram1 (l : ℝ) : List StationaryPulse :=
  [coreLift1 d, (coreHorizontal d 1).scale (l-1), (coreLift1 d).scale (-1/l)]

theorem tripleProgram0_on {l r s : ℝ} (hl : l ≠ 0)
    (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (hlr : |l*r| ≤ 1/2) :
    runProgram (tripleProgram0 d l) ![5+r,6+s,5] = ![5+l*r,6+s,5] := by
  have h₁ : (coreLift0 d).apply ![5+r,6+s,5] = ![5+r,6+s,5+r] := by
    rw [StationaryPulse.apply, coreLift0_on d hr hs]
    ext i; fin_cases i <;> simp [basis]
  have h₂ : ((coreHorizontal d 0).scale (l-1)).apply ![5+r,6+s,5+r] =
      ![5+l*r,6+s,5+r] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreHorizontal_on d 0 _ _ hr]
    ext i; fin_cases i <;> simp [basis]
    ring
  have h₃ : ((coreLift0 d).scale (-1/l)).apply ![5+l*r,6+s,5+r] = ![5+l*r,6+s,5] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreLift0_on d hlr hs]
    ext i; fin_cases i <;> simp [basis]
    field_simp [hl]
    ring
  change ((coreLift0 d).scale (-1/l)).apply
    (((coreHorizontal d 0).scale (l-1)).apply ((coreLift0 d).apply ![5+r,6+s,5])) = _
  rw [h₁, h₂, h₃]

theorem tripleProgram1_on {l r s : ℝ} (hl : l ≠ 0)
    (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (hls : |l*s| ≤ 1/2) :
    runProgram (tripleProgram1 d l) ![5+r,6+s,5] = ![5+r,6+l*s,5] := by
  have h₁ : (coreLift1 d).apply ![5+r,6+s,5] = ![5+r,6+s,5+s] := by
    rw [StationaryPulse.apply, coreLift1_on d hr hs]
    ext i; fin_cases i <;> simp [basis]
  have h₂ : ((coreHorizontal d 1).scale (l-1)).apply ![5+r,6+s,5+s] =
      ![5+r,6+l*s,5+s] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreHorizontal_on d 1 _ _ hs]
    ext i; fin_cases i <;> simp [basis]
    ring
  have h₃ : ((coreLift1 d).scale (-1/l)).apply ![5+r,6+l*s,5+s] = ![5+r,6+l*s,5] := by
    rw [StationaryPulse.apply, StationaryPulse.scale_field, coreLift1_on d hr hls]
    ext i; fin_cases i <;> simp [basis]
    field_simp [hl]
    ring
  change ((coreLift1 d).scale (-1/l)).apply
    (((coreHorizontal d 1).scale (l-1)).apply ((coreLift1 d).apply ![5+r,6+s,5])) = _
  rw [h₁, h₂, h₃]

def processingProgram (l m : ℝ) : List StationaryPulse :=
  tripleProgram0 d l ++ tripleProgram1 d m

theorem processingProgram_on {l m r s : ℝ} (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : |r| ≤ 1/2) (hs : |s| ≤ 1/2) (hlr : |l*r| ≤ 1/2) (hms : |m*s| ≤ 1/2) :
    runProgram (processingProgram d l m) ![5+r,6+s,5] = ![5+l*r,6+m*s,5] := by
  rw [processingProgram, runProgram_append, tripleProgram0_on d hl hr hs hlr,
    tripleProgram1_on d hm hlr hs hms]

theorem processingProgram_off (l m : ℝ) (x : Space)
    (hx : x 1 ∈ Set.Icc 2 3) (hz : x 2 = 2) :
    runProgram (processingProgram d l m) x = x := by
  apply runProgram_fixed
  intro p hp
  simp only [processingProgram, tripleProgram0, tripleProgram1, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    simp [coreLift0_off d x hx, coreLift1_off d x hx, coreHorizontal_off d _ x hz]

end Solenoidal
end
end

end OAI
