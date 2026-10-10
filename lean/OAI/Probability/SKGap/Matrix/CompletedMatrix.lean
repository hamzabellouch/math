import Mathlib
import OAI.Probability.SKGap.Localization.IntegrableLinearCombinationSq
import OAI.Probability.SKGap.Localization.ProdEventSectionLaw

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
namespace SKGapCutoff.Regression

local instance {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

noncomputable def completedMatrix {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (g : (Fin n × Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  revealedCompletion U Y + residualProjection U*goe g*residualProjection U

lemma completedMatrix_symmetric {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (hY : Uᵀ*Y=Yᵀ*U) (g : (Fin n × Fin n) → ℝ) :
    (completedMatrix U Y g)ᵀ=completedMatrix U Y g := by
  simp only [completedMatrix,Matrix.transpose_add,Matrix.transpose_mul,
    revealedCompletion_symmetric U Y hY,residualProjection_symmetric,goe_symmetric,
    Matrix.mul_assoc]

lemma completedMatrix_answer {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U) (g : (Fin n × Fin n) → ℝ) :
    completedMatrix U Y g*U=Y := by
  rw [completedMatrix,Matrix.add_mul,revealedCompletion_answer U Y hU hY,
    Matrix.mul_assoc,residualProjection_mul U hU,Matrix.mul_zero,add_zero]

lemma mul_extendFrame {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ) :
    A*extendFrame U q=extendFrame (A*U) (A *ᵥ q) := by
  funext i a
  obtain rfl | ⟨a,rfl⟩ := Fin.eq_zero_or_eq_succ a
  · rfl
  · rfl

lemma extendedProjection_mul_old {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (ho : Uᵀ *ᵥ q=0) :
    residualProjection (extendFrame U q)*residualProjection U=
      residualProjection (extendFrame U q) := by
  have hqU : (queryColumn q)ᵀ*U=0 := by
    ext a b
    fin_cases a
    have hh := congrFun ho b
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,queryColumn,Matrix.mulVec,
      dotProduct,Matrix.zero_apply,Pi.zero_apply,mul_comm] using hh
  have hqP : (queryColumn q)ᵀ*residualProjection U=(queryColumn q)ᵀ := by
    rw [residualProjection,Matrix.mul_sub,Matrix.mul_one,
      ← Matrix.mul_assoc,hqU,Matrix.zero_mul,sub_zero]
  rw [extendFrame_projection,queryComplement,Matrix.sub_mul,
    residualProjection_idem U hU,Matrix.mul_assoc,hqP]

lemma old_mul_extendedProjection {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (ho : Uᵀ *ᵥ q=0) :
    residualProjection U*residualProjection (extendFrame U q)=
      residualProjection (extendFrame U q) := by
  have hh := congrArg Matrix.transpose (extendedProjection_mul_old U q hU ho)
  simpa only [Matrix.transpose_mul,residualProjection_symmetric] using hh

lemma completedMatrix_new_residual {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (ho : Uᵀ *ᵥ q=0)
    (g : (Fin n × Fin n) → ℝ) :
    residualProjection (extendFrame U q)*completedMatrix U Y g*
      residualProjection (extendFrame U q)=
      residualProjection (extendFrame U q)*goe g*residualProjection (extendFrame U q) := by
  let P := residualProjection U
  let Q := residualProjection (extendFrame U q)
  have hQP : Q*P=Q := extendedProjection_mul_old U q hU ho
  have hPQ : P*Q=Q := old_mul_extendedProjection U q hU ho
  have hR : Q*revealedCompletion U Y*Q=0 := by
    calc
      _ = Q*(P*revealedCompletion U Y*P)*Q := by
        simp only [← Matrix.mul_assoc,hQP]
        rw [Matrix.mul_assoc (Q*revealedCompletion U Y) P Q,hPQ]
      _ = 0 := by rw [revealedCompletion_residual U Y hU,Matrix.mul_zero,Matrix.zero_mul]
  change Q*(revealedCompletion U Y+P*goe g*P)*Q=Q*goe g*Q
  rw [Matrix.mul_add,Matrix.add_mul,hR,zero_add]
  simp only [← Matrix.mul_assoc,hQP]
  rw [Matrix.mul_assoc (Q*goe g) P Q,hPQ]

theorem completedMatrix_update {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U) (ho : Uᵀ *ᵥ q=0)
    (g : (Fin n × Fin n) → ℝ) :
    completedMatrix U Y g =
      revealedCompletion (extendFrame U q) (extendFrame Y (completedMatrix U Y g *ᵥ q))+
      residualProjection (extendFrame U q)*goe g*residualProjection (extendFrame U q) := by
  have hh := regression_decomposition (completedMatrix U Y g) (extendFrame U q)
    (completedMatrix_symmetric U Y hY g)
  simpa only [mul_extendFrame,completedMatrix_answer U Y hU hY,
    revealedCompletion,completedMatrix_new_residual U Y q hU ho] using hh

lemma completedMatrix_new_compatibility {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U) (g : (Fin n × Fin n) → ℝ) :
    (extendFrame U q)ᵀ*extendFrame Y (completedMatrix U Y g *ᵥ q)=
      (extendFrame Y (completedMatrix U Y g *ᵥ q))ᵀ*extendFrame U q := by
  have he : completedMatrix U Y g*extendFrame U q=
      extendFrame Y (completedMatrix U Y g *ᵥ q) := by
    rw [mul_extendFrame,completedMatrix_answer U Y hU hY g]
  rw [← he,Matrix.transpose_mul,completedMatrix_symmetric U Y hY g,Matrix.mul_assoc]

lemma completedMatrix_input_decomposition {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U) (v : Fin n → ℝ)
    (g : (Fin n × Fin n) → ℝ) :
    completedMatrix U Y g *ᵥ v = Y *ᵥ (Uᵀ *ᵥ v)+
      completedMatrix U Y g *ᵥ (residualProjection U *ᵥ v) := by
  simp only [residualProjection,Matrix.sub_mulVec,Matrix.one_mulVec,
    Matrix.mulVec_sub,Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc,completedMatrix_answer U Y hU hY g]
  abel

@[fun_prop] lemma measurable_revealedCompletion {n r : ℕ} :
    Measurable (fun z : Matrix (Fin n) (Fin r) ℝ × Matrix (Fin n) (Fin r) ℝ =>
      revealedCompletion z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [revealedCompletion,Matrix.add_apply,Matrix.sub_apply,
    Matrix.mul_apply,Matrix.transpose_apply]
  fun_prop

@[fun_prop] lemma measurable_extendFrame {n r : ℕ} :
    Measurable (fun z : Matrix (Fin n) (Fin r) ℝ × (Fin n → ℝ) => extendFrame z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro a
  obtain rfl | ⟨a,rfl⟩ := Fin.eq_zero_or_eq_succ a
  · exact (measurable_pi_apply i).comp measurable_snd
  · exact (measurable_pi_apply a).comp ((measurable_pi_apply i).comp measurable_fst)

theorem completedMatrix_regeneration {n r : ℕ} (hn : 0 < n) {H : Type*}
    [MeasurableSpace H] (ρ : Measure H) [SFinite ρ]
    (U Y : H → Matrix (Fin n) (Fin r) ℝ) (q : H → Fin n → ℝ)
    (hUm : Measurable U) (hYm : Measurable Y) (hqm : Measurable q)
    (hU : ∀ h, (U h)ᵀ*U h=1) (hY : ∀ h, (U h)ᵀ*Y h=(Y h)ᵀ*U h)
    (hq : ∀ h, ∑ i, q h i^2=1) (ho : ∀ h, (U h)ᵀ *ᵥ q h=0) :
    let p := fun h => U h *ᵥ ((Y h)ᵀ *ᵥ q h)
    (ρ.prod (standardArrayLaw (Fin n × Fin n))).map
      (fun z => ((z.1,completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1),
        completedMatrix (U z.1) (Y z.1) z.2)) =
    ((answerHistoryLaw ρ (fun h => residualProjection (U h)) q).prod
      (standardArrayLaw (Fin n × Fin n))).map
      (fun z => ((z.1.1,p z.1.1+z.1.2),
        completedMatrix (extendFrame (U z.1.1) (q z.1.1))
          (extendFrame (Y z.1.1) (p z.1.1+z.1.2)) z.2)) := by
  dsimp only
  let P := fun h => residualProjection (U h)
  let p := fun h => U h *ᵥ ((Y h)ᵀ *ᵥ q h)
  have hU' : Measurable (fun h => fun i j => U h i j) := hUm
  have hY' : Measurable (fun h => fun i j => Y h i j) := hYm
  have hPm : Measurable P := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    simp only [P,residualProjection,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply]
    fun_prop
  have hpm : Measurable p := by
    apply Measurable.of_eval
    intro i
    simp only [p,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
    fun_prop
  have hPq h : P h *ᵥ q h=q h := by
    dsimp [P,residualProjection]
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec,ho,
      Matrix.mulVec_zero,sub_zero]
  have hPqc h : P h*queryColumn (q h)=queryColumn (q h) := by
    ext i a
    fin_cases a
    exact congrFun (hPq h) i
  have hj := adaptive_query_regeneration hn ρ P q hPm hqm
    (fun h => residualProjection_symmetric (U h))
    (fun h => residualProjection_idem (U h) (hU h)) hq hPqc
  let out : (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) →
      (H × (Fin n → ℝ)) × Matrix (Fin n) (Fin n) ℝ := fun z =>
    ((z.1.1,p z.1.1+z.1.2),
      revealedCompletion (extendFrame (U z.1.1) (q z.1.1))
        (extendFrame (Y z.1.1) (p z.1.1+z.1.2))+Matrix.of (fun i j => z.2 (i,j)))
  have hout : Measurable out := by
    have ha : Measurable (fun z : (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) =>
        p z.1.1+z.1.2) := (hpm.comp measurable_fst.fst).add measurable_fst.snd
    have hu' : Measurable (fun z : (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) =>
        extendFrame (U z.1.1) (q z.1.1)) := measurable_extendFrame.comp
      ((hUm.comp measurable_fst.fst).prodMk (hqm.comp measurable_fst.fst))
    have hy' : Measurable (fun z : (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) =>
        extendFrame (Y z.1.1) (p z.1.1+z.1.2)) := measurable_extendFrame.comp ((hYm.comp measurable_fst.fst).prodMk ha)
    have hc := measurable_revealedCompletion.comp (hu'.prodMk hy')
    apply (measurable_fst.fst.prodMk ha).prodMk
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (((measurable_pi_apply j).comp (measurable_pi_apply i)).comp hc).add
      ((measurable_pi_apply (i,j)).comp measurable_snd)
  have hmL : Measurable (fun z : H × ((Fin n × Fin n) → ℝ) =>
      ((z.1, queryAnswer (P z.1) (q z.1) z.2),queryResidual (P z.1) (q z.1) z.2)) :=
    (measurable_fst.prodMk (measurable_queryAnswer_comp _ _ _
      (hPm.comp measurable_fst) (hqm.comp measurable_fst) measurable_snd)).prodMk
      (measurable_queryResidual_comp _ _ _ (hPm.comp measurable_fst)
        (hqm.comp measurable_fst) measurable_snd)
  have hmR : Measurable (fun z : (H × (Fin n → ℝ)) × ((Fin n × Fin n) → ℝ) =>
      (z.1,queryResidual (P z.1.1) (q z.1.1) z.2)) :=
    measurable_fst.prodMk (measurable_queryResidual_comp _ _ _
      (hPm.comp measurable_fst.fst) (hqm.comp measurable_fst.fst) measurable_snd)
  have he := congrArg (Measure.map out) hj
  rw [Measure.map_map hout hmL,Measure.map_map hout hmR] at he
  have hof (A : Matrix (Fin n) (Fin n) ℝ) : Matrix.of (fun i j => A i j)=A := rfl
  have hpoint (z : H × ((Fin n × Fin n) → ℝ)) : out ((z.1,queryAnswer (P z.1) (q z.1) z.2),
      queryResidual (P z.1) (q z.1) z.2) =
      ((z.1,completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1),
        completedMatrix (U z.1) (Y z.1) z.2) := by
    have ha := completed_query_answer (U z.1) (Y z.1) (q z.1) z.2 (ho z.1) (hPq z.1)
    change completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1=p z.1+queryAnswer (P z.1) (q z.1) z.2 at ha
    dsimp only [out]
    rw [← ha]
    congr 1
    simpa only [extendFrame_projection,P,queryResidual,hof] using
      (completedMatrix_update (U z.1) (Y z.1) (q z.1) (hU z.1) (hY z.1) (ho z.1) z.2).symm
  simp_rw [Function.comp_def,hpoint] at he
  simpa only [out,completedMatrix,queryResidual,← extendFrame_projection,P,p,hof] using he

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
