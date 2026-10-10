import Mathlib
import OAI.Probability.SKGap.Matrix.MeasurableCompletedMatrix

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
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise
namespace SKGapCutoff.Regression

local instance transferMatrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

lemma extendFrame_compatible {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q b : Fin n → ℝ) (hY : Uᵀ*Y=Yᵀ*U) (hb : Uᵀ *ᵥ b=Yᵀ *ᵥ q) :
    (extendFrame U q)ᵀ*extendFrame Y b=(extendFrame Y b)ᵀ*extendFrame U q := by
  ext a c
  obtain rfl | ⟨a,rfl⟩ := Fin.eq_zero_or_eq_succ a
  · obtain rfl | ⟨c,rfl⟩ := Fin.eq_zero_or_eq_succ c
    · simp only [Matrix.mul_apply,Matrix.transpose_apply,extendFrame_zero,mul_comm]
    · have hh := congrFun hb c
      simpa only [Matrix.mul_apply,Matrix.transpose_apply,extendFrame_zero,extendFrame_succ,
        Matrix.mulVec,dotProduct,mul_comm] using hh.symm
  · obtain rfl | ⟨c,rfl⟩ := Fin.eq_zero_or_eq_succ c
    · have hh := congrFun hb a
      simpa only [Matrix.mul_apply,Matrix.transpose_apply,extendFrame_zero,extendFrame_succ,
        Matrix.mulVec,dotProduct] using hh
    · exact congrFun (congrFun hY a) c

lemma queryInnovation_perpendicular {n r : ℕ} (U : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (ho : Uᵀ *ᵥ q=0)
    (g : (Fin n ⊕ Unit) → ℝ) :
    Uᵀ *ᵥ queryInnovation (residualProjection U) q g=0 := by
  have he : queryInnovation (residualProjection U) q g =
      (Real.sqrt n)⁻¹ •
        (queryComplement (residualProjection U) q *ᵥ (fun k => g (Sum.inl k))+
          (Real.sqrt 2*g (Sum.inr ())) • q) := by
    ext i
    simp only [queryInnovation,Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
    ring
  have hR : Uᵀ*queryComplement (residualProjection U) q=0 := by
    rw [← extendFrame_projection]
    have hp : Uᵀ*residualProjection U=0 := mul_residualProjection U hU
    simp only [extendFrame_projection,queryComplement,Matrix.mul_sub,← Matrix.mul_assoc,hp]
    have hcol : Uᵀ*queryColumn q=0 := by
      ext a b
      fin_cases b
      exact congrFun ho a
    rw [hcol,Matrix.zero_mul,sub_zero]
  rw [he,Matrix.mulVec_smul,Matrix.mulVec_add,Matrix.mulVec_smul,
    Matrix.mulVec_mulVec,hR,Matrix.zero_mulVec,ho,smul_zero,add_zero,smul_zero]

lemma regenerated_frame_compatible {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (hU : Uᵀ*U=1) (hY : Uᵀ*Y=Yᵀ*U)
    (ho : Uᵀ *ᵥ q=0) (g : (Fin n ⊕ Unit) → ℝ) :
    let b := U *ᵥ (Yᵀ *ᵥ q)+queryInnovation (residualProjection U) q g
    (extendFrame U q)ᵀ*extendFrame Y b=(extendFrame Y b)ᵀ*extendFrame U q := by
  apply extendFrame_compatible U Y q _ hY
  rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,hU,Matrix.one_mulVec,
    queryInnovation_perpendicular U q hU ho g,add_zero]

@[fun_prop] lemma measurable_completedMatrix_comp {n r : ℕ} {H : Type*} [MeasurableSpace H]
    (U Y : H → Matrix (Fin n) (Fin r) ℝ) (g : H → (Fin n × Fin n) → ℝ)
    (hU : Measurable U) (hY : Measurable Y) (hg : Measurable g) :
    Measurable (fun h => completedMatrix (U h) (Y h) (g h)) := by
  have hU' : Measurable (fun h i j => U h i j) := hU
  have hY' : Measurable (fun h i j => Y h i j) := hY
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [completedMatrix,revealedCompletion,residualProjection,goe,
    Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply]
  fun_prop

@[fun_prop] lemma measurable_matrix_mulVec_comp {n m : ℕ} {H : Type*} [MeasurableSpace H]
    (A : H → Matrix (Fin n) (Fin m) ℝ) (v : H → Fin m → ℝ)
    (hA : Measurable A) (hv : Measurable v) : Measurable (fun h => A h *ᵥ v h) := by
  have hA' : Measurable (fun h i j => A h i j) := hA
  apply Measurable.of_eval
  intro i
  simp only [Matrix.mulVec,dotProduct]
  fun_prop

noncomputable def regeneratedAnswer {n r : ℕ} (U Y : Matrix (Fin n) (Fin r) ℝ)
    (q : Fin n → ℝ) (g : (Fin n ⊕ Unit) → ℝ) : Fin n → ℝ :=
  U *ᵥ (Yᵀ *ᵥ q)+queryInnovation (residualProjection U) q g

@[fun_prop] lemma measurable_regeneratedAnswer_comp {n r : ℕ} {H : Type*} [MeasurableSpace H]
    (U Y : H → Matrix (Fin n) (Fin r) ℝ) (q : H → Fin n → ℝ)
    (g : H → (Fin n ⊕ Unit) → ℝ)
    (hU : Measurable U) (hY : Measurable Y) (hq : Measurable q) (hg : Measurable g) :
    Measurable (fun h => regeneratedAnswer (U h) (Y h) (q h) (g h)) := by
  have hY' : Measurable (fun h => (Y h)ᵀ) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact ((measurable_pi_apply i).comp (measurable_pi_apply j)).comp hY
  exact (measurable_matrix_mulVec_comp U _ hU
    (measurable_matrix_mulVec_comp _ q hY' hq)).add
    (measurable_queryInnovation_comp _ q g (measurable_residualProjection_comp U hU) hq hg)

lemma regeneration_event_le {n r : ℕ} (hn : 0 < n) {H : Type*} [MeasurableSpace H]
    (ρ : Measure H) (U Y : H → Matrix (Fin n) (Fin r) ℝ) (q : H → Fin n → ℝ)
    (hUm : Measurable U) (hYm : Measurable Y) (hqm : Measurable q)
    (G : Set H) (hG : MeasurableSet G)
    (hgood : ∀ h ∈ G, (U h)ᵀ*U h=1 ∧ (U h)ᵀ*Y h=(Y h)ᵀ*U h ∧
      (∑ i, q h i^2)=1 ∧ (U h)ᵀ *ᵥ q h=0)
    (T : Set (H × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ))) (hT : MeasurableSet T) :
    (ρ.prod ((standardArrayLaw (Fin n × Fin n)).prod (standardArrayLaw (Fin n ⊕ Unit))))
      ((fun z => (z.1,(regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2,
        completedMatrix (extendFrame (U z.1) (q z.1))
          (extendFrame (Y z.1) (regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2)) z.2.1))) ⁻¹' T) ≤
    (ρ.prod (standardArrayLaw (Fin n × Fin n)))
      ((fun z => (z.1,(completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1,
        completedMatrix (U z.1) (Y z.1) z.2))) ⁻¹' T)+ρ Gᶜ := by
  let F : H × ((Fin n × Fin n) → ℝ) →
      H × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) := fun z =>
    (z.1,(completedMatrix (U z.1) (Y z.1) z.2 *ᵥ q z.1,
      completedMatrix (U z.1) (Y z.1) z.2))
  let R : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) →
      H × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ) := fun z =>
    (z.1,(regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2,
      completedMatrix (extendFrame (U z.1) (q z.1))
        (extendFrame (Y z.1) (regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2)) z.2.1))
  have hA : Measurable (fun z : H × ((Fin n × Fin n) → ℝ) =>
      completedMatrix (U z.1) (Y z.1) z.2) :=
    measurable_completedMatrix_comp _ _ _ (hUm.comp measurable_fst) (hYm.comp measurable_fst) measurable_snd
  have hF : Measurable F := measurable_fst.prodMk
    ((measurable_matrix_mulVec_comp _ _ hA (hqm.comp measurable_fst)).prodMk hA)
  have hb : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2) :=
    measurable_regeneratedAnswer_comp _ _ _ _ (hUm.comp measurable_fst)
      (hYm.comp measurable_fst) (hqm.comp measurable_fst) (measurable_snd.comp measurable_snd)
  have hUn : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      extendFrame (U z.1) (q z.1)) :=
    measurable_extendFrame.comp ((hUm.comp measurable_fst).prodMk (hqm.comp measurable_fst))
  have hYn : Measurable (fun z : H × (((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ)) =>
      extendFrame (Y z.1) (regeneratedAnswer (U z.1) (Y z.1) (q z.1) z.2.2)) :=
    measurable_extendFrame.comp ((hYm.comp measurable_fst).prodMk hb)
  have hR : Measurable R := measurable_fst.prodMk (hb.prodMk
    (measurable_completedMatrix_comp _ _ _ hUn hYn (measurable_fst.comp measurable_snd)))
  apply prod_event_le_of_section_law ρ
    ((standardArrayLaw (Fin n × Fin n)).prod (standardArrayLaw (Fin n ⊕ Unit)))
    (standardArrayLaw (Fin n × Fin n)) R F hR hF G hG _ T hT
  intro h hh
  have hsec := completedMatrix_section_law hn (U h) (Y h) (q h)
    (hgood h hh).1 (hgood h hh).2.1 (hgood h hh).2.2.1 (hgood h hh).2.2.2
  have hfo : Measurable (fun g => (completedMatrix (U h) (Y h) g *ᵥ q h,
      completedMatrix (U h) (Y h) g)) :=
    measurable_snd.comp (hF.comp measurable_prodMk_left)
  have hro : Measurable (fun z : ((Fin n × Fin n) → ℝ) × ((Fin n ⊕ Unit) → ℝ) => (regeneratedAnswer (U h) (Y h) (q h) z.2,
      completedMatrix (extendFrame (U h) (q h))
        (extendFrame (Y h) (regeneratedAnswer (U h) (Y h) (q h) z.2)) z.1)) :=
    measurable_snd.comp (hR.comp measurable_prodMk_left)
  have hout : Measurable (fun t : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => (h,t)) :=
    measurable_const.prodMk measurable_id
  have he := congrArg (Measure.map (fun t : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ => (h,t))) hsec
  have hmfo := Measure.map_map (μ := standardArrayLaw (Fin n × Fin n)) hout hfo
  have hmro := Measure.map_map (μ := (standardArrayLaw (Fin n × Fin n)).prod
    (standardArrayLaw (Fin n ⊕ Unit))) hout hro
  exact hmro.symm.trans (he.symm.trans hmfo)

theorem regenerated_exponentiallyRare
    {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (r : ℕ)
    (U Y : ∀ n, H n → Matrix (Fin n) (Fin r) ℝ)
    (q : ∀ n, H n → Fin n → ℝ)
    (hUm : ∀ n, Measurable (U n)) (hYm : ∀ n, Measurable (Y n))
    (hqm : ∀ n, Measurable (q n))
    (G : ∀ n, Set (H n)) (hG : ∀ n, MeasurableSet (G n))
    (hrare : ExponentiallyRare ρ (fun n => (G n)ᶜ))
    (hgood : ∀ᶠ n in atTop, ∀ h ∈ G n,
      (U n h)ᵀ*U n h=1 ∧ (U n h)ᵀ*Y n h=(Y n h)ᵀ*U n h ∧
        (∑ i, q n h i^2)=1 ∧ (U n h)ᵀ *ᵥ q n h=0)
    (T : ∀ n, Set (H n × ((Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ)))
    (hT : ∀ n, MeasurableSet (T n))
    (hbad : ExponentiallyRare (fun n => (ρ n).prod (standardArrayLaw (Fin n × Fin n)))
      (fun n => (fun z => (z.1,(completedMatrix (U n z.1) (Y n z.1) z.2 *ᵥ q n z.1,
        completedMatrix (U n z.1) (Y n z.1) z.2))) ⁻¹' T n)) :
    ExponentiallyRare
      (fun n => (ρ n).prod ((standardArrayLaw (Fin n × Fin n)).prod
        (standardArrayLaw (Fin n ⊕ Unit))))
      (fun n => (fun z => (z.1,(regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2.2,
        completedMatrix (extendFrame (U n z.1) (q n z.1))
          (extendFrame (Y n z.1)
            (regeneratedAnswer (U n z.1) (Y n z.1) (q n z.1) z.2.2)) z.2.1))) ⁻¹' T n) := by
  apply exponentiallyRare_of_measure_le_add _ _ ρ _ _ _ hbad hrare
  filter_upwards [hgood,eventually_gt_atTop 0] with n hn hn0
  exact regeneration_event_le hn0 (ρ n) (U n) (Y n) (q n)
    (hUm n) (hYm n) (hqm n) (G n) (hG n) hn (T n) (hT n)

end SKGapCutoff.Regression

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix Matrix.Norms.Elementwise

end

end OAI
