import Mathlib
import OAI.Analysis.Conductivity.Variational.ContDiffClmDet

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology

def localPullback {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (x : E) : V := by
  classical
  exact if x ∈ X.source then f (X x) else 0

lemma localPullback_support {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) :
    Function.support (localPullback X f) ⊆ X.symm '' (Function.support f ∩ X.target) := by
  intro x hx
  have hxs : x ∈ X.source := by
    by_contra hn
    exact hx (by simp [localPullback, hn])
  refine ⟨X x, ⟨?_, X.map_source hxs⟩, X.left_inv hxs⟩
  simpa only [Function.mem_support, localPullback, ite_eq_left hxs] using hx

lemma localPullback_tsupport {E V : Type*} [TopologicalSpace E] [T2Space E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) (hf : HasCompactSupport f)
    (hs : tsupport f ⊆ X.target) :
    HasCompactSupport (localPullback X f) ∧
      tsupport (localPullback X f) ⊆ X.symm '' tsupport f ∧
      tsupport (localPullback X f) ⊆ X.source := by
  have hK := hf.image_of_continuousOn (X.symm.continuousOn.mono hs)
  have hsub : Function.support (localPullback X f) ⊆ X.symm '' tsupport f :=
    (localPullback_support X f).trans (image_mono (fun _ hx => subset_closure hx.1))
  have ht : tsupport (localPullback X f) ⊆ X.symm '' tsupport f :=
    closure_minimal hsub hK.isClosed
  refine ⟨HasCompactSupport.of_support_subset_isCompact hK hsub, ht, ?_⟩
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := ht hx
  exact X.map_target (hs hy)

lemma localPullback_contDiff {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : OpenPartialHomeomorph E E) (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (f : E → V) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ X.target) : ContDiff ℝ (↑(⊤ : ℕ∞)) (localPullback X f) := by
  apply contDiff_of_contDiffOn_tsupport X.open_source _
    (localPullback_tsupport X f hfc hfs).2.2
  intro x hx
  have hxs := hx
  have heq : localPullback X f =ᶠ[𝓝 x] f ∘ X := by
    filter_upwards [X.open_source.mem_nhds hxs] with y hy
    simp only [localPullback, ite_eq_left hy, Function.comp_apply]
  exact ((hf.contDiffAt.comp x ((hX x hxs).contDiffAt
    (X.open_source.mem_nhds hxs))).congr_of_eventuallyEq heq).contDiffWithinAt

lemma localPullback_comp {E V : Type*} [TopologicalSpace E] [Zero V]
    (X : OpenPartialHomeomorph E E) (f : E → V) {z : E} (hz : z ∈ X.target) :
    localPullback X f (X.symm z) = f z := by
  simp only [localPullback, ite_eq_left (X.map_target hz), X.right_inv hz]

lemma localPullback_bounds {E : Type*} [TopologicalSpace E]
    (X : OpenPartialHomeomorph E E) (f : E → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ localPullback X f x ∧ localPullback X f x ≤ 1 := by
  intro x
  by_cases hx : x ∈ X.source
  · simpa only [localPullback, ite_eq_left hx] using hf (X x)
  · simp only [localPullback, ite_eq_right hx, le_refl, zero_le_one, and_self]

end ScalarConductivity

end

end OAI
