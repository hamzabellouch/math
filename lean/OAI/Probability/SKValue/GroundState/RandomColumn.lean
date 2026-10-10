import Mathlib
import OAI.Probability.SKValue.GroundState.ColumnBounds

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {Ω ι κ ν : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  [Fintype κ] [Fintype ν] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma measurable_finiteMaximum {f : Ω → ι → ℝ} (hf : ∀ i,Measurable (fun ω ↦ f ω i)) :
    Measurable (fun ω ↦ finiteMaximum (f ω)) :=
  continuous_finiteMaximum.measurable.comp (Measurable.of_eval hf)

omit [IsProbabilityMeasure μ] in
lemma integrable_randomMaximum [IsProbabilityMeasure μ] {f : Ω → ι → ℝ}
    (hf : ∀ i,Integrable (fun ω ↦ f ω i) μ) :
    Integrable (fun ω ↦ finiteMaximum (f ω)) μ := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (hf i).abs)).mono'
    (continuous_finiteMaximum.comp_aestronglyMeasurable
      ((integrable_pi_iff.mpr hf).aestronglyMeasurable))
  exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using abs_finiteMaximum_le (f ω))

omit [Fintype ι] [Nonempty ι] in
lemma random_linear_integrable [Fintype ι] [Nonempty ι] (a : Ω → ι → ν → ℝ)
    (ha : ∀ i k,Measurable (fun ω ↦ a ω i k)) (C : ℝ)
    (hC : ∀ ω i k,|a ω i k|≤C) (i : ι) :
    Integrable (fun p : Ω×(ν → ℝ) ↦ linearProcess (a p.1) p.2 i)
      (μ.prod (gaussianProduct ν)) := by
  unfold linearProcess
  apply integrable_finsetSum
  intro k _
  apply ((gaussian_coordinate_integrable k).abs.const_mul C |>.comp_snd μ).mono'
    (((ha i k).comp measurable_fst).mul ((measurable_pi_apply k).comp measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall (fun p ↦ by
    change |a p.1 i k * p.2 k| ≤ C * |p.2 k|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hC p.1 i k) (abs_nonneg _))

lemma measurable_quadraticValue (w : Ω → ι → EuclideanSpace ℝ κ) (d : Ω → ι → ℝ)
    (hw : ∀ i,Measurable (fun ω ↦ w ω i)) (hd : ∀ i,Measurable (fun ω ↦ d ω i)) :
    Measurable (fun ω ↦ quadraticValue (w ω) (d ω)) := by
  have hm : Measurable (fun p : Ω×((κ×κ) → ℝ) ↦
      finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w p.1 i)) p.2 i+d p.1 i)) := by
    apply measurable_finiteMaximum
    intro i
    unfold linearProcess quadraticCoeff
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma random_quadratic_integrable (w : Ω → ι → EuclideanSpace ℝ κ) (d : Ω → ι → ℝ)
    (hw : ∀ i,Measurable (fun ω ↦ w ω i)) (hd : ∀ i,Integrable (fun ω ↦ d ω i) μ)
    (R : ℝ) (hR : ∀ ω i,‖w ω i‖≤R) :
    Integrable (fun ω ↦ quadraticValue (w ω) (d ω)) μ := by
  have hi : Integrable (fun p : Ω×((κ×κ) → ℝ) ↦
      finiteMaximum (fun i ↦ linearProcess (fun i ↦ quadraticCoeff (w p.1 i)) p.2 i+d p.1 i))
      (μ.prod (gaussianProduct (κ×κ))) := by
    apply integrable_randomMaximum
    intro i
    apply Integrable.add _ ((hd i).comp_fst _)
    apply random_linear_integrable (fun ω i ↦ quadraticCoeff (w ω i)) _ (R^2) _ i
    · intro i k; unfold quadraticCoeff; fun_prop
    · intro ω i k
      exact (quadraticCoeff_coord_bound _ _).trans (sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) (hR ω i)) |>.mpr (hR ω i))
  exact hi.integral_prod_left

lemma columnVector_coord_bound {v : EuclideanSpace ℝ κ} (hv : v=0 ∨ ⟪v,v⟫=1)
    (w : EuclideanSpace ℝ κ) (k : κ) : |columnVector v w k|≤‖w‖^2 :=
  (PiLp.norm_apply_le _ k).trans (columnVector_norm_le hv w)

theorem random_column_identity (w : Ω → ι → EuclideanSpace ℝ κ) (d : Ω → ι → ℝ)
    (v : Ω → EuclideanSpace ℝ κ) (hw : ∀ i,Measurable (fun ω ↦ w ω i))
    (_hdm : ∀ i,Measurable (fun ω ↦ d ω i))
    (hd : ∀ i,Integrable (fun ω ↦ d ω i) μ) (hv : Measurable v)
    (hu : ∀ ω,v ω=0 ∨ ⟪v ω,v ω⟫=1) (R : ℝ) (hR : ∀ ω i,‖w ω i‖≤R) :
    (∫ ω,quadraticValue (w ω) (d ω) ∂μ)=
      ∫ p : Ω×(κ → ℝ),quadraticValue (fun i ↦ columnResidual (v p.1) (w p.1 i))
        (fun i ↦ d p.1 i+linearProcess (fun i k ↦ columnVector (v p.1) (w p.1 i) k) p.2 i)
        ∂μ.prod (gaussianProduct κ) := by
  have hw' (i : ι) : Measurable (fun p : Ω×(κ → ℝ) ↦ columnResidual (v p.1) (w p.1 i)) :=
    measurable_columnResidual (hv.comp measurable_fst) ((hw i).comp measurable_fst)
  have hd' (i : ι) : Integrable (fun p : Ω×(κ → ℝ) ↦
      d p.1 i+linearProcess (fun i k ↦ columnVector (v p.1) (w p.1 i) k) p.2 i)
      (μ.prod (gaussianProduct κ)) := by
    apply ((hd i).comp_fst _).add
    apply random_linear_integrable (fun ω i k ↦ columnVector (v ω) (w ω i) k) _ (R^2) _ i
    · intro i k
      exact (PiLp.continuous_apply 2 (fun _ : κ ↦ ℝ) k).measurable.comp (measurable_columnVector hv (hw i))
    · intro ω i k
      exact (columnVector_coord_bound (hu ω) _ _).trans
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hR ω i))).mpr (hR ω i))
  have hi := random_quadratic_integrable _ _ hw' hd' R
    (fun p i ↦ (columnResidual_norm_le (hu p.1) (w p.1 i)).trans (hR p.1 i))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω ↦ quadraticValue_column (w ω) (d ω) (v ω) (hu ω))

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable (κ : Type*) [Fintype κ]

abbrev ColumnHistory (j : ℕ) := Fin j → κ → ℝ
noncomputable def columnHistoryLaw (j : ℕ) : Measure (ColumnHistory κ j) :=
  Measure.pi (fun _ ↦ gaussianProduct κ)
instance (j : ℕ) : IsProbabilityMeasure (columnHistoryLaw κ j) := by
  unfold columnHistoryLaw; infer_instance

def historyInit {j : ℕ} (h : ColumnHistory κ (j+1)) : ColumnHistory κ j := fun i ↦ h i.castSucc

def historySplit (j : ℕ) : ColumnHistory κ (j+1) ≃ᵐ ColumnHistory κ j × (κ → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j+1) ↦ κ → ℝ) (Fin.last j)).trans
    MeasurableEquiv.prodComm

omit [Fintype κ] in
lemma historySplit_apply [Fintype κ] (j : ℕ) (h : ColumnHistory κ (j+1)) :
    historySplit κ j h=(historyInit κ h,h (Fin.last j)) := by
  simp [historySplit,MeasurableEquiv.piFinSuccAbove,Fin.insertNthEquiv]
  rfl

lemma historySplit_preserving (j : ℕ) :
    MeasurePreserving (historySplit κ j) (columnHistoryLaw κ (j+1))
      ((columnHistoryLaw κ j).prod (gaussianProduct κ)) := by
  exact (Measure.measurePreserving_swap).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (j+1) ↦ gaussianProduct κ) (Fin.last j))

omit [Fintype κ] in
lemma historyInit_measurable [Fintype κ] (j : ℕ) : Measurable (historyInit κ (j:=j)) := by
  unfold historyInit; fun_prop

lemma history_integral_succ (j : ℕ) (f : ColumnHistory κ j × (κ → ℝ) → ℝ) :
    (∫ h,f (historyInit κ h,h (Fin.last j)) ∂columnHistoryLaw κ (j+1))=
      ∫ p,f p ∂(columnHistoryLaw κ j).prod (gaussianProduct κ) := by
  simpa only [historySplit_apply] using (historySplit_preserving κ j).integral_comp' f

lemma history_integrable_succ (j : ℕ) {f : ColumnHistory κ j × (κ → ℝ) → ℝ}
    (hf : Integrable f ((columnHistoryLaw κ j).prod (gaussianProduct κ))) :
    Integrable (fun h ↦ f (historyInit κ h,h (Fin.last j))) (columnHistoryLaw κ (j+1)) := by
  simpa only [Function.comp_def,historySplit_apply] using (historySplit_preserving κ j).integrable_comp
    hf.aestronglyMeasurable |>.mpr hf

end SKValueG

end

end OAI
