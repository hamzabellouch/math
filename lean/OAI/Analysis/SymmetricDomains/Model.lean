import Mathlib
import OAI.Analysis.SymmetricDomains.ModelChartOpen
import OAI.Analysis.SymmetricDomains.AffineProductCoordinates

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
open Set Complex
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def linearConjugateChart (e : E ≃L[ℂ] F) (f : OpenPartialHomeomorph E E) :
    OpenPartialHomeomorph F F :=
  (e.symm.toHomeomorph.toOpenPartialHomeomorph.trans f).trans
    e.toHomeomorph.toOpenPartialHomeomorph

@[simp] lemma linearConjugateChart_source (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) :
    (linearConjugateChart e f).source = e.symm ⁻¹' f.source := by
  simp [linearConjugateChart]

@[simp] lemma linearConjugateChart_target (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) :
    (linearConjugateChart e f).target = e.symm ⁻¹' f.target := by
  simp [linearConjugateChart]

@[simp] lemma linearConjugateChart_apply (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (x : F) :
    linearConjugateChart e f x = e (f (e.symm x)) := rfl

@[simp] lemma linearConjugateChart_symm_apply (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (x : F) :
    (linearConjugateChart e f).symm x = e (f.symm (e.symm x)) := rfl

lemma linearConjugateChart_analytic (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (ha : AnalyticOnNhd ℂ f f.source) :
    AnalyticOnNhd ℂ (linearConjugateChart e f) (linearConjugateChart e f).source := by
  intro x hx
  rw [linearConjugateChart_source] at hx
  exact (e.analyticAt _).comp ((ha _ hx).comp (e.symm.analyticAt x))

lemma linearConjugateChart_inverse_analytic (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (ha : AnalyticOnNhd ℂ f.symm f.target) :
    AnalyticOnNhd ℂ (linearConjugateChart e f).symm (linearConjugateChart e f).target := by
  intro x hx
  rw [linearConjugateChart_target] at hx
  exact (e.analyticAt _).comp ((ha _ hx).comp (e.symm.analyticAt x))

lemma linearConjugateChart_image (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (D : Set E) :
    linearConjugateChart e f '' (e '' D) = e '' (f '' D) := by
  simp only [Set.image_image]
  congr 1
  funext x
  simp

theorem model_bounded_biholomorph {m k : ℕ}
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {D : Set (Affine m × Affine (k+1))} (hD : IsOpen D) (hconn : IsConnected D)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ D, ∀ i, c*‖x.1‖^2 < e (fun t => (x.2 t).im) i) :
    ∃ B : Set (Affine (m+(k+1))), IsOpen B ∧ IsConnected B ∧ Bornology.IsBounded B ∧
      Nonempty (Biholomorph (affineProductCoordinates m (k+1) '' D) B) := by
  let a := affineProductCoordinates m (k+1)
  let f := modelBoundedChart (E := Affine m) e
  have hp := modelBoundedChart_bounded_open e hD hc hbound
  have hsub : D ⊆ f.source := hp.1
  have hf : AnalyticOnNhd ℂ f f.source := by
    intro x hx
    apply modelBoundedChart_analytic e
    exact hx.2
  have hfi : AnalyticOnNhd ℂ f.symm f.target := by
    intro x hx
    apply modelBoundedChart_inverse_analytic e
    exact hx.1
  have hsub' : a '' D ⊆ (linearConjugateChart a f).source := by
    rintro _ ⟨x,hx,rfl⟩
    simpa only [linearConjugateChart_source,mem_preimage,a.symm_apply_apply] using hsub hx
  let b : Biholomorph (a '' D) (linearConjugateChart a f '' (a '' D)) :=
    Biholomorph.ofOpenPartialHomeomorph (linearConjugateChart a f)
      (linearConjugateChart_analytic a f hf) (linearConjugateChart_inverse_analytic a f hfi)
      (a '' D) hsub'
  refine ⟨linearConjugateChart a f '' (a '' D),?_,?_,?_,⟨b⟩⟩
  · rw [linearConjugateChart_image]
    exact a.isOpenMap _ hp.2.1
  · rw [linearConjugateChart_image]
    exact (hconn.image f (f.continuousOn.mono hsub)).image a a.continuous.continuousOn
  · rw [linearConjugateChart_image]
    exact a.toContinuousLinearMap.lipschitzWith.isBounded_image hp.2.2

end Release061

end

end OAI
