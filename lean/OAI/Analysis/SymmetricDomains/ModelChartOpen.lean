import Mathlib
import OAI.Analysis.SymmetricDomains.SupportCayleyOpenImage
import OAI.Analysis.SymmetricDomains.ComplexifyRealContinuousEquiv

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
open Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def supportLinearCoordinates (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) :
    (E × (Fin (k+1) → ℂ)) ≃L[ℂ] (E × (Fin (k+1) → ℂ)) :=
  (ContinuousLinearEquiv.refl ℂ E).prodCongr (complexifyRealContinuousEquiv e)

@[simp] lemma supportLinearCoordinates_fst
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (x : E × (Fin (k+1) → ℂ)) :
    (supportLinearCoordinates e x).1 = x.1 := rfl

@[simp] lemma supportLinearCoordinates_im
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (x : E × (Fin (k+1) → ℂ))
    (i : Fin (k+1)) :
    ((supportLinearCoordinates e x).2 i).im = e (fun t => (x.2 t).im) i :=
  complexifyRealContinuousEquiv_im e x.2 i

def modelBoundedChart (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) :
    OpenPartialHomeomorph (E × (Fin (k+1) → ℂ)) (E × (Fin (k+1) → ℂ)) :=
  (supportLinearCoordinates e).toHomeomorph.toOpenPartialHomeomorph.trans supportCayleyChart

@[simp] lemma modelBoundedChart_apply
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (x : E × (Fin (k+1) → ℂ)) :
    modelBoundedChart e x = supportCayley (supportLinearCoordinates e x) := rfl

lemma modelBoundedChart_analytic
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, (supportLinearCoordinates e x).2 i+I ≠ 0) :
    AnalyticAt ℂ (modelBoundedChart e) x :=
  (analyticAt_supportCayley hx).comp ((supportLinearCoordinates e).toContinuousLinearMap.analyticAt x)

lemma modelBoundedChart_inverse_analytic
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {x : E × (Fin (k+1) → ℂ)} (hx : ∀ i, 1-x.2 i ≠ 0) :
    AnalyticAt ℂ (modelBoundedChart e).symm x := by
  change AnalyticAt ℂ (fun y => (supportLinearCoordinates (E := E) e).symm (supportUncayley y)) x
  exact ((supportLinearCoordinates (E := E) e).symm.toContinuousLinearMap.analyticAt _).comp
    (analyticAt_supportUncayley hx)

theorem modelBoundedChart_bounded_open
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {D : Set (E × (Fin (k+1) → ℂ))} (hD : IsOpen D)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ D, ∀ i, c*‖x.1‖^2 < e (fun t => (x.2 t).im) i) :
    D ⊆ (modelBoundedChart e).source ∧
    IsOpen (modelBoundedChart e '' D) ∧
    Bornology.IsBounded (modelBoundedChart e '' D) := by
  have hcoord : IsOpen (supportLinearCoordinates e '' D) :=
    (supportLinearCoordinates e).toHomeomorph.isOpenMap D hD
  have hupper : ∀ x ∈ supportLinearCoordinates e '' D, ∀ i,
      c*‖x.1‖^2 < (x.2 i).im := by
    rintro _ ⟨x,hx,rfl⟩ i
    simpa only [supportLinearCoordinates_fst,supportLinearCoordinates_im] using hbound x hx i
  have himage : modelBoundedChart e '' D =
      supportCayley '' (supportLinearCoordinates e '' D) := by
    rw [Set.image_image]
    rfl
  constructor
  · intro x hx
    change x ∈ Set.univ ∩ (supportLinearCoordinates e) ⁻¹' {y | ∀ i, y.2 i+I ≠ 0}
    refine ⟨Set.mem_univ _,fun i => ?_⟩
    apply add_I_ne_zero_of_im_pos
    simpa only [supportLinearCoordinates_im] using
      (mul_nonneg hc.le (sq_nonneg ‖x.1‖)).trans_lt (hbound x hx i)
  · rw [himage]
    refine ⟨supportCayley_open_image hcoord ?_,supportCayley_bounded hc hupper⟩
    intro x hx i
    exact (mul_nonneg hc.le (sq_nonneg ‖x.1‖)).trans_lt (hupper x hx i)

end Release061

end

end OAI
