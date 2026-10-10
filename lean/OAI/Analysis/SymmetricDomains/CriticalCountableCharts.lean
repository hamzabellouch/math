import Mathlib
import OAI.Analysis.SymmetricDomains.MaximizerBundleBorel

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

structure ActualCriticalChart {d N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (q : (Fin d → ℝ) → Affine N) where
  fiberDim : ℕ
  split : (Affine N →L[ℂ] ℂ) ≃L[ℝ] ((Fin d → ℝ) × (Fin fiberDim → ℝ))
  base : Set (Fin d → ℝ)
  isOpen_base : IsOpen base
  continuous_q : ContinuousOn q base
  smooth_param : ContDiffOn ℝ 1 (criticalBundleParam (realCriticalMatrix q) split
    (realCriticalConstant (parameterLogBase P ∘ q))) (base ×ˢ univ)
  range_param : ∀ x ∈ base, range (fun k => criticalBundleParam (realCriticalMatrix q) split
    (realCriticalConstant (parameterLogBase P ∘ q)) (x,k)) =
    {a | fderiv ℝ (fun y => parameterLogBase P (q y) + (a (q y)).re) x = 0}

namespace ActualCriticalChart
variable {d N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}
noncomputable def param (c : ActualCriticalChart P q) :
    (Fin d → ℝ) × (Fin c.fiberDim → ℝ) → (Affine N →L[ℂ] ℂ) :=
  criticalBundleParam (realCriticalMatrix q) c.split
    (realCriticalConstant (parameterLogBase P ∘ q))

def maxLocus (c : ActualCriticalChart P q) (K : Set (Affine N)) :
    Set ((Fin d → ℝ) × (Fin c.fiberDim → ℝ)) :=
  {p | p.1 ∈ c.base ∧ q p.1 ∈ K ∧ IsMaxOn (parameterPotential P (c.param p)) K (q p.1)}

lemma measurableSet_maxLocus (c : ActualCriticalChart P q) {K : Set (Affine N)} (hK : IsClosed K) :
    MeasurableSet (c.maxLocus K) :=
  actual_maximizer_bundle_borel P hK c.isOpen_base.measurableSet q c.continuous_q
    c.param c.smooth_param.continuousOn

lemma differentiableOn_param_maxLocus (c : ActualCriticalChart P q) (K : Set (Affine N)) :
    DifferentiableOn ℝ c.param (c.maxLocus K) :=
  (c.smooth_param.differentiableOn one_ne_zero).mono (fun _ hp => ⟨hp.1,mem_univ _⟩)

end ActualCriticalChart

theorem actual_critical_countable_charts {d N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hq : ContDiffOn ℝ 2 q B)
    (hP : ∀ x ∈ B, MvPolynomial.eval (q x) P ≠ 0)
    (hi : ∀ x ∈ B, Function.Injective (fderiv ℝ q x)) :
    ∃ C : Set (ActualCriticalChart P q), C.Countable ∧
      (∀ c ∈ C, c.base ⊆ B) ∧ B ⊆ ⋃ c ∈ C, c.base := by
  have hex (x : B) : ∃ c : ActualCriticalChart P q, x.val ∈ c.base ∧ c.base ⊆ B := by
    obtain ⟨r,e,W,hWo,hxW,hWB,hpar,hfib⟩ := actual_critical_bundle P B hB q hq hP x.property
      (hi x.val x.property)
    exact ⟨⟨r,e,W,hWo,hq.continuousOn.mono hWB,hpar,hfib⟩,hxW,hWB⟩
  choose c hc hcB using hex
  obtain ⟨T,hTc,hT⟩ := (HereditarilyLindelofSpace.isLindelof B).elim_countable_subcover
    (fun x : B => (c x).base) (fun x => (c x).isOpen_base) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,hc ⟨x,hx⟩⟩)
  refine ⟨c '' T,hTc.image c,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact hcB x
  · intro x hx
    obtain ⟨y,hyT,hxy⟩ := mem_iUnion₂.mp (hT hx)
    exact mem_iUnion₂.mpr ⟨c y,mem_image_of_mem c hyT,hxy⟩

end Release061

end

end OAI
