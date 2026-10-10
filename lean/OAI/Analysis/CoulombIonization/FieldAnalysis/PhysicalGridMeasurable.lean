import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.Vartheta

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

namespace CoulombNeumann
variable {N : ℕ}

def physicalGridPressure (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (x : (Fin N → CubeSpace)) : ℝ :=
  b⁻¹^2*cellPressure (cubeAssignment (fun a => (t a:ℝ)) (rotatedCubeCloud R (fun i => b⁻¹ • x i)))

lemma physicalGridPressure_nonneg (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (x : (Fin N → CubeSpace)) :
    0 ≤ physicalGridPressure b R t x := mul_nonneg (sq_nonneg _) (cellPressure_nonneg _)
lemma physicalGridPressure_le (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (x : (Fin N → CubeSpace)) :
    physicalGridPressure b R t x ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ) :=
  mul_le_mul_of_nonneg_left (cellPressure_le _) (sq_nonneg _)

lemma physicalGridCloud_continuous (b : ℝ) :
    Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      rotatedCubeCloud p.1.1 (fun i => b⁻¹ • p.2 i)) := by
  have hx : Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      fun i => b⁻¹ • p.2 i) :=
    continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).const_smul b⁻¹)
  have hr : Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) => p.1.1) := by fun_prop
  have hh : Continuous (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      (p.1.1,fun i => b⁻¹ • p.2 i)) := hr.prodMk hx
  have hcomp := (rotatedCubeCloud_continuous (N := N)).comp hh
  simpa only [Function.comp_def] using hcomp

lemma physicalGridCell_measurable (b : ℝ) :
    Measurable (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      cellPressure (cubeAssignment (fun a => (p.1.2 a:ℝ))
        (rotatedCubeCloud p.1.1 (fun i => b⁻¹ • p.2 i)))) := by
  have ht : Measurable (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) =>
      fun a => (p.1.2 a:ℝ)) :=
    cube_t_continuous.measurable.comp (measurable_snd.comp measurable_fst)
  have hin := ht.prodMk (physicalGridCloud_continuous (N := N) b).measurable
  have hcomp := (cubePressure_measurable (N := N)).comp hin
  simpa only [Function.comp_def] using hcomp

lemma physicalGridPressure_measurable (b : ℝ) :
    Measurable (fun p : (CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace) => physicalGridPressure b p.1.1 p.1.2 p.2) := by
  unfold physicalGridPressure
  exact (physicalGridCell_measurable (N := N) b).const_mul (b⁻¹^2)

lemma physicalGridPressure_fixed_measurable (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) :
    Measurable (physicalGridPressure (N := N) b R t) := by
  let f : (Fin N → CubeSpace) → ((CubeRotation × (Fin 3 → I)) × (Fin N → CubeSpace)) := fun x => ((R,t),x)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  have hcomp := (physicalGridPressure_measurable (N := N) b).comp hf
  simpa only [Function.comp_def,f] using hcomp

end CoulombNeumann

end

end OAI
