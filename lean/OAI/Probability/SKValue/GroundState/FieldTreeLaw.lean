import Mathlib
import OAI.Probability.SKValue.GroundState.TreeProductLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def fieldNoiseLaw (n : ℕ) : Measure ((Fin n → ℝ)×ℝ) :=
  (gaussianProduct (Fin n)).prod gumbelLaw
instance fieldNoiseLaw_probability (n : ℕ) : IsProbabilityMeasure (fieldNoiseLaw n) := by
  unfold fieldNoiseLaw; infer_instance

noncomputable def fieldTreeEval (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ)
    (w : TreeEdges T → (Fin n → ℝ)×ℝ) : ℝ :=
  fieldTreeValue n q T x (fun p ↦ (w p.2).1 p.1) (fun e ↦ (w e).2)

lemma continuous_fieldTreeEval (n : ℕ) (q : ℝ) (T : GaussianTree) :
    Continuous (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦ fieldTreeEval n q T p.1 p.2) := by
  unfold fieldTreeEval fieldTreeValue treeOffset leafField linearProcess
  apply continuous_finiteMaximum.comp
  apply continuous_pi
  intro α
  fun_prop

lemma fieldTreeEval_nil (n : ℕ) (q : ℝ) (x : Fin n → ℝ) (w : TreeEdges [] → (Fin n → ℝ)×ℝ) :
    fieldTreeEval n q [] x w=∑ i,|x i| := by
  simp only [fieldTreeEval,fieldTreeValue,treeOffset,treeCenter,linearProcess,leafField]
  simp only [show ∀ f : PEmpty → ℝ, (∑ e,f e)=0 from fun f ↦ Fintype.sum_empty f,
    sub_self,add_zero,finiteMaximum_const]

noncomputable def fieldChildLaw (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) : Measure ℝ :=
  ((gaussianProduct (Fin n)).prod (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n))).map
    (fun p ↦ fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2)

lemma continuous_fieldChild (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    Continuous (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
      fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2) := by
  have hc : Continuous (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
      ((fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i),p.2)) := by
    apply Continuous.prodMk _ continuous_snd
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul ((continuous_apply i).comp continuous_fst))
  exact (continuous_fieldTreeEval n l.endpoint T).comp hc

instance fieldChildLaw_probability (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    IsProbabilityMeasure (fieldChildLaw n q l T x) := by
  unfold fieldChildLaw
  infer_instance

lemma fieldTreeEval_step (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ)
    (w : TreeEdges (l::T) → (Fin n → ℝ)×ℝ) :
    fieldTreeEval n q (l::T) x w=branchMax l.height l.branchExcess
      ((fun j ↦ fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*(w (Sum.inl j)).1 i)
        (fun e ↦ w (Sum.inr (j,e)))),fun j ↦ (w (Sum.inl j)).2) := by
  rw [fieldTreeEval,fieldTreeValue_step]
  unfold branchMax
  have he (a b : ℝ) : a+(b-Real.log (l.branchExcess+1 : ℝ))/l.height=
      (a+b/l.height)+(-Real.log (l.branchExcess+1 : ℝ)/l.height) := by ring
  conv_lhs => arg 1; ext j; rw [he]
  rw [finiteMaximum_add_const]
  simp only [fieldTreeEval,sub_eq_add_neg,neg_div]

lemma fieldTreeEval_law_step (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    MeasurePreserving (fieldTreeEval n q (l::T) x)
      (Measure.pi (fun _ : TreeEdges (l::T) ↦ fieldNoiseLaw n))
      (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) := by
  let σ := Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)
  have hc : MeasurePreserving (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
      fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2)
      ((gaussianProduct (Fin n)).prod σ) (fieldChildLaw n q l T x) :=
    ⟨(continuous_fieldChild n q l T x).measurable,rfl⟩
  have hb := (hc.prod (MeasurePreserving.id gumbelLaw)).comp
    (measurePreserving_midSwap (gaussianProduct (Fin n)) gumbelLaw σ)
  have hblocks := measurePreserving_nodeBlocks (I := Fin (l.branchExcess+1)) (E := TreeEdges T) (fieldNoiseLaw n)
  have hchildren := measurePreserving_pi (fun _ : Fin (l.branchExcess+1) ↦
    (fieldNoiseLaw n).prod σ) (fun _ ↦ (fieldChildLaw n q l T x).prod gumbelLaw) (fun _ ↦ hb)
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (l.branchExcess+1))
    (fun _ ↦ fieldChildLaw n q l T x) (fun _ ↦ gumbelLaw)
  have hmax : MeasurePreserving (branchMax l.height l.branchExcess)
      ((Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ fieldChildLaw n q l T x)).prod
        (Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ gumbelLaw)))
      (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) :=
    ⟨(continuous_branchMax _ _).measurable,rfl⟩
  have hall := hmax.comp (hp.comp (hchildren.comp hblocks))
  convert hall using 1
  funext w
  exact fieldTreeEval_step n q l T x w

lemma fieldTreeEval_integrable (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ) :
    Integrable (fieldTreeEval n q T x) (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) := by
  have hz (e : TreeEdges T) (i : Fin n) : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).1 i)
      (Measure.pi (fun _ ↦ fieldNoiseLaw n)) := by
    have h := ((measurePreserving_eval (fun _ : Fin n ↦ standardGaussian) i).integrable_comp (by fun_prop)).mpr
      standardGaussian_integrable_id
    exact (measurePreserving_eval (fun _ : TreeEdges T ↦ fieldNoiseLaw n) e).integrable_comp (by fun_prop)
      |>.mpr (h.comp_fst gumbelLaw)
  have hg (e : TreeEdges T) : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).2)
      (Measure.pi (fun _ ↦ fieldNoiseLaw n)) :=
    (measurePreserving_eval (fun _ : TreeEdges T ↦ fieldNoiseLaw n) e).integrable_comp (by fun_prop)
      |>.mpr (gumbel_integrable.comp_snd (gaussianProduct (Fin n)))
  unfold fieldTreeEval fieldTreeValue
  apply integrable_finiteMaximum_of_integrable
  intro α
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    apply Integrable.abs
    apply Integrable.add (integrable_const _)
    unfold leafField
    apply integrable_finsetSum
    intro e _
    exact (hz e i).const_mul _
  · unfold treeOffset linearProcess
    apply Integrable.sub _ (integrable_const _)
    apply integrable_finsetSum
    intro e _
    exact (hg e).const_mul _

lemma fieldTreeEval_comp_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (n : ℕ) (q : ℝ) (T : GaussianTree)
    (x : Ω → Fin n → ℝ) (w : Ω → TreeEdges T → (Fin n → ℝ)×ℝ)
    (hx : ∀ i,Integrable (fun ω ↦ x ω i) μ)
    (hz : ∀ e i,Integrable (fun ω ↦ (w ω e).1 i) μ)
    (hg : ∀ e,Integrable (fun ω ↦ (w ω e).2) μ) :
    Integrable (fun ω ↦ fieldTreeEval n q T (x ω) (w ω)) μ := by
  unfold fieldTreeEval fieldTreeValue
  apply integrable_finiteMaximum_of_integrable
  intro α
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    apply Integrable.abs
    apply Integrable.add (hx i)
    unfold leafField
    apply integrable_finsetSum
    intro e _
    exact (hz e i).const_mul _
  · unfold treeOffset linearProcess
    apply Integrable.sub _ (integrable_const _)
    apply integrable_finsetSum
    intro e _
    exact (hg e).const_mul _

lemma fieldChildLaw_integrable (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    Integrable (fun y : ℝ ↦ y) (fieldChildLaw n q l T x) := by
  rw [fieldChildLaw,integrable_map_measure (by fun_prop) (continuous_fieldChild n q l T x).measurable.aemeasurable]
  apply fieldTreeEval_comp_integrable
  · intro i
    apply Integrable.add (integrable_const _)
    exact ((integrable_comp_eval (μ := fun _ : Fin n ↦ standardGaussian) standardGaussian_integrable_id).const_mul _).comp_fst _
  · intro e i
    have h : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).1 i)
        (Measure.pi (fun _ ↦ fieldNoiseLaw n)) :=
      (integrable_comp_eval (μ := fun _ : TreeEdges T ↦ fieldNoiseLaw n)
        ((integrable_comp_eval (μ := fun _ : Fin n ↦ standardGaussian) (i := i) standardGaussian_integrable_id).comp_fst gumbelLaw))
    exact h.comp_snd _
  · intro e
    have h : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).2)
        (Measure.pi (fun _ ↦ fieldNoiseLaw n)) :=
      integrable_comp_eval (gumbel_integrable.comp_snd (gaussianProduct (Fin n)))
    exact h.comp_snd _

end SKValueG

end

end OAI
