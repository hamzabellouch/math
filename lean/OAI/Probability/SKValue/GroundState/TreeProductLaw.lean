import Mathlib
import OAI.Probability.SKValue.GroundState.TreeGuerra
import OAI.Probability.SKValue.GroundState.BranchLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma measurePreserving_finite_curry {I E A : Type*} [Fintype I] [Fintype E]
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : I×E → A ↦ fun i e ↦ z (i,e))
      (Measure.pi (fun _ ↦ μ)) (Measure.pi (fun _ : I ↦ Measure.pi (fun _ : E ↦ μ))) := by
  refine ⟨by fun_prop,?_⟩
  have h := Measure.infinitePi_map_curry (fun (_ : I) (_ : E) ↦ μ)
  simp only [Measure.infinitePi_eq_pi,MeasurableEquiv.coe_curry] at h
  convert h using 1
  rfl

lemma measurePreserving_nodeBlocks {I E A : Type*} [Fintype I] [Fintype E]
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : I⊕(I×E) → A ↦ fun i ↦ (z (Sum.inl i),fun e ↦ z (Sum.inr (i,e))))
      (Measure.pi (fun _ ↦ μ))
      (Measure.pi (fun _ : I ↦ μ.prod (Measure.pi (fun _ : E ↦ μ)))) := by
  have hsum := measurePreserving_sumPiEquivProdPi (fun _ : I⊕(I×E) ↦ μ)
  have hc := (MeasurePreserving.id (Measure.pi (fun _ : I ↦ μ))).prod
    (measurePreserving_finite_curry (I := I) (E := E) μ)
  have hp := (measurePreserving_arrowProdEquivProdArrow A (E → A) I
    (fun _ ↦ μ) (fun _ ↦ Measure.pi (fun _ : E ↦ μ))).symm
  exact hp.comp (hc.comp hsum)

lemma measurePreserving_midSwap {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (σ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite σ] :
    MeasurePreserving (fun p : (A×B)×C ↦ ((p.1.1,p.2),p.1.2))
      ((μ.prod ν).prod σ) ((μ.prod σ).prod ν) := by
  have h1 := measurePreserving_prodAssoc μ ν σ
  have h2 := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := σ))
  have h3 := (measurePreserving_prodAssoc μ σ ν).symm
  exact h3.comp (h2.comp h1)

noncomputable def gaussianAddLaw (c : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  (standardGaussian.prod μ).map (fun p : ℝ×ℝ ↦ c*p.1+p.2)

instance gaussianAddLaw_probability (c : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (gaussianAddLaw c μ) := by
  unfold gaussianAddLaw
  infer_instance

lemma gaussianAddLaw_integrable (c : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (fun x : ℝ ↦ x) (gaussianAddLaw c μ) := by
  rw [gaussianAddLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  exact ((standardGaussian_integrable_id.const_mul c).comp_fst μ).add (hi.comp_snd _)

lemma gaussianAddLaw_exp_integrable (c a : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) :
    Integrable (fun x : ℝ ↦ Real.exp (a*x)) (gaussianAddLaw c μ) := by
  rw [gaussianAddLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  have hg : Integrable (fun z : ℝ ↦ Real.exp ((a*c)*z)) standardGaussian :=
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a*c)
  convert hg.mul_prod hi using 1
  funext p
  dsimp only [Function.comp_def]
  rw [←Real.exp_add]
  congr 1
  ring

lemma gaussianAddLaw_exp (c a : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    (∫ x,Real.exp (a*x) ∂gaussianAddLaw c μ)=
      Real.exp ((a*c)^2/2)*(∫ x,Real.exp (a*x) ∂μ) := by
  rw [gaussianAddLaw,integral_map (by fun_prop) (by fun_prop)]
  have he (p : ℝ×ℝ) : Real.exp (a*(c*p.1+p.2))=
      Real.exp ((a*c)*p.1)*Real.exp (a*p.2) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_prod_mul (fun z : ℝ ↦ Real.exp ((a*c)*z)) (fun x : ℝ ↦ Real.exp (a*x))]
  have heq := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (a*c)
  simpa [mgf,standardGaussian] using congrArg (fun x ↦ x*(∫ x,Real.exp (a*x) ∂μ)) heq

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

noncomputable def edgeNoiseLaw : Measure (ℝ×ℝ) := standardGaussian.prod gumbelLaw
instance edgeNoiseLaw_probability : IsProbabilityMeasure edgeNoiseLaw := by
  unfold edgeNoiseLaw; infer_instance

noncomputable def scalarTreeLaw (c : ℝ → TreeLevel → ℝ) (q : ℝ) : GaussianTree → Measure ℝ
  | [] => Measure.dirac 0
  | l::T => branchLaw (gaussianAddLaw (c q l) (scalarTreeLaw c l.endpoint T)) l.height l.branchExcess

instance scalarTreeLaw_probability (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    IsProbabilityMeasure (scalarTreeLaw c q T) := by
  induction T generalizing q with
  | nil => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | cons l T ih =>
    have := ih l.endpoint
    exact inferInstanceAs (IsProbabilityMeasure
      (branchLaw (gaussianAddLaw (c q l) (scalarTreeLaw c l.endpoint T)) l.height l.branchExcess))

noncomputable def scalarTreeEval (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree)
    (w : TreeEdges T → ℝ×ℝ) : ℝ :=
  scalarTreeValue c q T (fun e ↦ (w e).1) (fun e ↦ (w e).2)

lemma finiteMaximum_const {I : Type*} [Fintype I] [Nonempty I] (a : ℝ) :
    finiteMaximum (fun _ : I ↦ a)=a := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum (fun _ : I ↦ a)
  exact hi.symm

lemma scalarTreeEval_nil (c : ℝ → TreeLevel → ℝ) (q : ℝ) (w : TreeEdges [] → ℝ×ℝ) :
    scalarTreeEval c q [] w=0 := by
  simp only [scalarTreeEval,scalarTreeValue,treeOffset,treeCenter,linearProcess]
  simp only [show ∀ f : PEmpty → ℝ, (∑ e,f e)=0 from fun f ↦ Fintype.sum_empty f,
    sub_self,zero_add,finiteMaximum_const]

lemma continuous_scalarTreeEval (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Continuous (scalarTreeEval c q T) := by
  unfold scalarTreeEval scalarTreeValue treeOffset
  apply continuous_finiteMaximum.comp
  apply continuous_pi
  intro α
  unfold linearProcess
  fun_prop

lemma marked_gaussianAddLaw {S : Type*} [MeasurableSpace S] (σ : Measure S) [IsProbabilityMeasure σ]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : S → ℝ}
    (hf : MeasurePreserving f σ μ) (c : ℝ) :
    MeasurePreserving (fun p : (ℝ×ℝ)×S ↦ (c*p.1.1+f p.2,p.1.2))
      (edgeNoiseLaw.prod σ) ((gaussianAddLaw c μ).prod gumbelLaw) := by
  have hadd : MeasurePreserving (fun p : ℝ×ℝ ↦ c*p.1+p.2)
      (standardGaussian.prod μ) (gaussianAddLaw c μ) := ⟨by fun_prop,rfl⟩
  exact ((hadd.prod (MeasurePreserving.id gumbelLaw)).comp
    (((MeasurePreserving.id standardGaussian).prod hf).prod (MeasurePreserving.id gumbelLaw))).comp
    (measurePreserving_midSwap standardGaussian gumbelLaw σ)

lemma scalarTreeEval_step (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (w : TreeEdges (l::T) → ℝ×ℝ) :
    scalarTreeEval c q (l::T) w=branchMax l.height l.branchExcess
      ((fun i ↦ c q l*(w (Sum.inl i)).1+
        scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))),
       fun i ↦ (w (Sum.inl i)).2) := by
  rw [scalarTreeEval,scalarTreeValue_step]
  unfold branchMax
  have he (i : Fin (l.branchExcess+1)) :
      c q l*(w (Sum.inl i)).1+scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))+
        ((w (Sum.inl i)).2-Real.log (l.branchExcess+1 : ℝ))/l.height=
      (c q l*(w (Sum.inl i)).1+scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))+
        (w (Sum.inl i)).2/l.height)+(-Real.log (l.branchExcess+1 : ℝ)/l.height) := by ring
  change finiteMaximum (fun i ↦ c q l*(w (Sum.inl i)).1+
    scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))+
      ((w (Sum.inl i)).2-Real.log (l.branchExcess+1 : ℝ))/l.height)=_
  conv_lhs => arg 1; ext i; rw [he i]
  rw [finiteMaximum_add_const]
  ring

theorem scalarTreeEval_law (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    MeasurePreserving (scalarTreeEval c q T) (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw))
      (scalarTreeLaw c q T) := by
  induction T generalizing q with
  | nil =>
    have he : scalarTreeEval c q []=fun _ ↦ (0 : ℝ) := funext (scalarTreeEval_nil c q)
    rw [he,scalarTreeLaw]
    exact ⟨measurable_const,by simp⟩
  | cons l T ih =>
    let ν := gaussianAddLaw (c q l) (scalarTreeLaw c l.endpoint T)
    have hblock := measurePreserving_nodeBlocks (I := Fin (l.branchExcess+1)) (E := TreeEdges T) edgeNoiseLaw
    have hchild := marked_gaussianAddLaw (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)) (ih l.endpoint) (c q l)
    have hchildren := measurePreserving_pi (fun _ : Fin (l.branchExcess+1) ↦
      edgeNoiseLaw.prod (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)))
      (fun _ ↦ ν.prod gumbelLaw) (fun _ ↦ hchild)
    have hpair := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (l.branchExcess+1))
      (fun _ ↦ ν) (fun _ ↦ gumbelLaw)
    have hmax : MeasurePreserving (branchMax l.height l.branchExcess)
        ((Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ ν)).prod
          (Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ gumbelLaw)))
        (scalarTreeLaw c q (l::T)) := ⟨(continuous_branchMax _ _).measurable,rfl⟩
    have hall := hmax.comp (hpair.comp (hchildren.comp hblock))
    convert hall using 1
    funext w
    exact scalarTreeEval_step c q l T w

lemma scalarTreeLaw_integrable (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Integrable (fun x : ℝ ↦ x) (scalarTreeLaw c q T) := by
  induction T generalizing q with
  | nil =>
    change Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))
    exact integrable_dirac (by simp)
  | cons l T ih => exact branchLaw_integrable (gaussianAddLaw_integrable _ (ih l.endpoint)) _ _

end SKValueG

end

end OAI
