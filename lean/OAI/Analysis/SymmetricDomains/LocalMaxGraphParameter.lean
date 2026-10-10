import Mathlib
import OAI.Analysis.SymmetricDomains.LogarithmicPeakBound

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Module

theorem exists_complex_parameter_conormal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (T : Submodule ℝ V) (f : T.dualAnnihilator) :
    ∃ a : E →L[ℂ] ℂ, (∀ x ∈ T, (a x.val).re = 0) ∧
      ∀ v : V, (a v.val).re = f.val v := by
  obtain ⟨g,hg⟩ := conormalRestriction_surjective V T f
  let a : E →L[ℂ] ℂ := StrongDual.extendRCLike (𝕜 := ℂ) g.val.toContinuousLinearMap
  have ha : ∀ x : E, (a x).re = g.val x := by
    intro x
    exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) g.val.toContinuousLinearMap x
  refine ⟨a,?_,?_⟩
  · intro x hx
    rw [ha]
    exact (Submodule.mem_dualAnnihilator _).mp g.property x.val ⟨x,hx,rfl⟩
  · intro v
    rw [ha]
    exact congrArg (fun h : T.dualAnnihilator => h.val v) hg

end

open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def graphCriticalParameter (φ : E → ℝ) (g : E → F)
    (q : E × (F →L[ℝ] ℝ)) : (E →L[ℝ] ℝ) × (F →L[ℝ] ℝ) :=
  (-fderiv ℝ φ q.1 - q.2.comp (fderiv ℝ g q.1),q.2)

theorem graphCriticalParameter_iff (φ : E → ℝ) (g : E → F)
    (s : E) (a : (E →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) :
    (∀ v, fderiv ℝ φ s v + a.1 v + a.2 (fderiv ℝ g s v) = 0) ↔
      a = graphCriticalParameter φ g (s,a.2) := by
  constructor
  · intro h
    apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro v
      simp only [graphCriticalParameter,sub_apply,
        neg_apply,ContinuousLinearMap.comp_apply]
      linarith [h v]
    · rfl
  · intro h v
    have h' := congrArg (fun q => q.1 v) h
    simp only [graphCriticalParameter,sub_apply,
      neg_apply,ContinuousLinearMap.comp_apply] at h'
    linarith

def graphCriticalEquiv (φ : E → ℝ) (g : E → F) :
    (E × (F →L[ℝ] ℝ)) ≃ {q : E × ((E →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) |
      ∀ v, fderiv ℝ φ q.1 v + q.2.1 v + q.2.2 (fderiv ℝ g q.1 v) = 0} where
  toFun q := ⟨(q.1,graphCriticalParameter φ g q),
    (graphCriticalParameter_iff φ g q.1 _).mpr rfl⟩
  invFun q := (q.val.1,q.val.2.2)
  left_inv _ := rfl
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((graphCriticalParameter_iff φ g q.val.1 q.val.2).mp q.property).symm

theorem differentiableAt_graphCriticalParameter [CompleteSpace F]
    {φ : E → ℝ} {g : E → F} {s : E}
    (hφ : AnalyticAt ℝ φ s) (hg : AnalyticAt ℝ g s) (b : F →L[ℝ] ℝ) :
    DifferentiableAt ℝ (graphCriticalParameter φ g) (s,b) := by
  have hφ' : DifferentiableAt ℝ (fun q : E × (F →L[ℝ] ℝ) => fderiv ℝ φ q.1) (s,b) :=
    hφ.fderiv.differentiableAt.comp (s,b) differentiableAt_fst
  have hg' : DifferentiableAt ℝ (fun q : E × (F →L[ℝ] ℝ) => fderiv ℝ g q.1) (s,b) :=
    hg.fderiv.differentiableAt.comp (s,b) differentiableAt_fst
  exact (hφ'.neg.sub (differentiableAt_snd.clm_comp hg')).prodMk differentiableAt_snd

def selfDualGraphParameter (e : E ≃L[ℝ] (E →L[ℝ] ℝ)) (φ : E → ℝ) (g : E → F)
    (q : E × (F →L[ℝ] ℝ)) : E × (F →L[ℝ] ℝ) :=
  (e.symm (graphCriticalParameter φ g q).1,(graphCriticalParameter φ g q).2)

theorem differentiableAt_selfDualGraphParameter [CompleteSpace F]
    (e : E ≃L[ℝ] (E →L[ℝ] ℝ)) {φ : E → ℝ} {g : E → F} {s : E}
    (hφ : AnalyticAt ℝ φ s) (hg : AnalyticAt ℝ g s) (b : F →L[ℝ] ℝ) :
    DifferentiableAt ℝ (selfDualGraphParameter e φ g) (s,b) := by
  have h := differentiableAt_graphCriticalParameter hφ hg b
  exact (e.symm.differentiableAt.comp (s,b) h.fst).prodMk h.snd

theorem graph_weight_hasFDerivAt {φ : E → ℝ} {g : E → F} {s : E}
    (hφ : DifferentiableAt ℝ φ s) (hg : DifferentiableAt ℝ g s)
    (a : (E →L[ℝ] ℝ) × (F →L[ℝ] ℝ)) :
    HasFDerivAt (fun x => φ x + a.1 x + a.2 (g x))
      (fderiv ℝ φ s + a.1 + a.2.comp (fderiv ℝ g s)) s :=
  (hφ.hasFDerivAt.add a.1.hasFDerivAt).add (a.2.hasFDerivAt.comp s hg.hasFDerivAt)

theorem localMax_graph_parameter {φ : E → ℝ} {g : E → F} {s : E}
    (hφ : DifferentiableAt ℝ φ s) (hg : DifferentiableAt ℝ g s)
    (a : (E →L[ℝ] ℝ) × (F →L[ℝ] ℝ))
    (hmax : IsLocalMax (fun x => φ x+a.1 x+a.2 (g x)) s) :
    a = graphCriticalParameter φ g (s,a.2) := by
  apply (graphCriticalParameter_iff φ g s a).mp
  have he := hmax.hasFDerivAt_eq_zero (graph_weight_hasFDerivAt hφ hg a)
  intro v
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) he

end Release061

end

end OAI
