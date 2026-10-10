import Mathlib
import OAI.Probability.SKGap.Matrix.CompletedMatrix

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
open scoped BigOperators
open Filter Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
namespace SKGapCutoff.Regression

local instance completedMatrixMeasurableSpace {n m : ℕ} :
    MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

@[fun_prop] lemma measurable_completedMatrix {n r : ℕ} :
    Measurable (fun z : (Matrix (Fin n) (Fin r) ℝ × Matrix (Fin n) (Fin r) ℝ) ×
        ((Fin n × Fin n) → ℝ) => completedMatrix z.1.1 z.1.2 z.2) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [completedMatrix,revealedCompletion,residualProjection,goe,
    Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply]
  fun_prop

@[fun_prop] lemma measurable_revealedCompletion_comp {n r : ℕ} {H : Type*}
    [MeasurableSpace H] (U Y : H → Matrix (Fin n) (Fin r) ℝ)
    (hU : Measurable U) (hY : Measurable Y) :
    Measurable (fun h => revealedCompletion (U h) (Y h)) := by
  have hU' : Measurable (fun h i j => U h i j) := hU
  have hY' : Measurable (fun h i j => Y h i j) := hY
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [revealedCompletion,Matrix.add_apply,Matrix.sub_apply,
    Matrix.mul_apply,Matrix.transpose_apply]
  fun_prop

theorem completedMatrix_section_law {n r : ℕ} (hn : 0 < n)
    (U Y : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U)
    (hq : ∑ i, q i^2=1) (ho : Uᵀ *ᵥ q=0) :
    let p := U *ᵥ (Yᵀ *ᵥ q)
    (standardArrayLaw (Fin n × Fin n)).map
      (fun g => (completedMatrix U Y g *ᵥ q,completedMatrix U Y g)) =
    ((standardArrayLaw (Fin n × Fin n)).prod (standardArrayLaw (Fin n ⊕ Unit))).map
      (fun z => (p+queryInnovation (residualProjection U) q z.2,
        completedMatrix (extendFrame U q)
          (extendFrame Y (p+queryInnovation (residualProjection U) q z.2)) z.1)) := by
  dsimp only
  let P := residualProjection U
  let p := U *ᵥ (Yᵀ *ᵥ q)
  have hPq : P *ᵥ q=q := by
    simp only [P,residualProjection,Matrix.sub_mulVec,Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec,ho,Matrix.mulVec_zero,sub_zero]
  have hqc : P*queryColumn q=queryColumn q := by
    ext i a
    fin_cases a
    exact congrFun hPq i
  have hj := query_joint_law hn P (residualProjection_symmetric U)
    (residualProjection_idem U hU) q hq hqc
  let out : ((Fin n × Fin n) → ℝ) × (Fin n → ℝ) →
      (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ := fun z =>
    (p+z.2,revealedCompletion (extendFrame U q) (extendFrame Y (p+z.2))+
      Matrix.of (fun i j => z.1 (i,j)))
  have ha : Measurable (fun z : ((Fin n × Fin n) → ℝ) × (Fin n → ℝ) => p+z.2) :=
    measurable_const.add measurable_snd
  have hy : Measurable (fun z : ((Fin n × Fin n) → ℝ) × (Fin n → ℝ) =>
      extendFrame Y (p+z.2)) := measurable_extendFrame.comp (measurable_const.prodMk ha)
  have hc : Measurable (fun z : ((Fin n × Fin n) → ℝ) × (Fin n → ℝ) =>
      revealedCompletion (extendFrame U q) (extendFrame Y (p+z.2))) :=
    measurable_revealedCompletion_comp _ _ measurable_const hy
  have hout : Measurable out := by
    apply ha.prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (((measurable_pi_apply j).comp (measurable_pi_apply i)).comp hc).add
      ((measurable_pi_apply (i,j)).comp measurable_fst)
  have hm1 := (queryResidual_measurable P q).prodMk (queryAnswer_measurable P q)
  have hm2 : Measurable (fun z : ((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ) =>
      (queryResidual P q z.1,queryInnovation P q z.2)) :=
    ((queryResidual_measurable P q).comp measurable_fst).prodMk
      ((queryInnovation_measurable P q).comp measurable_snd)
  have he := congrArg (Measure.map out) hj
  rw [Measure.map_map hout hm1,Measure.map_map hout hm2] at he
  have hof (A : Matrix (Fin n) (Fin n) ℝ) : Matrix.of (fun i j => A i j)=A := rfl
  have hpoint g : out (queryResidual P q g,queryAnswer P q g)=
      (completedMatrix U Y g *ᵥ q,completedMatrix U Y g) := by
    have ha := completed_query_answer U Y q g ho hPq
    change completedMatrix U Y g *ᵥ q=p+queryAnswer P q g at ha
    dsimp only [out]
    rw [← ha]
    congr 1
    simpa only [extendFrame_projection,P,queryResidual,hof] using
      (completedMatrix_update U Y q hU hY ho g).symm
  simp_rw [Function.comp_def,hpoint] at he
  simpa only [out,completedMatrix,queryResidual,← extendFrame_projection,P,p,hof] using he

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
