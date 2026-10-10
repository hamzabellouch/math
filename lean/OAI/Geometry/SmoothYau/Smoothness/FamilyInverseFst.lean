import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section FiberInverse
variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
variable (e : OpenPartialHomeomorph (P × E) (P × E))
    (he : ∀ w, (e w).1 = w.1)

include he in
lemma familyInverse_fst {w : P × E} (hw : w ∈ e.target) :
    (e.symm w).1 = w.1 := by
  have h := he (e.symm w)
  rw [e.right_inv hw] at h
  exact h.symm

def fiberOpenPartialHomeomorph (q : P) : OpenPartialHomeomorph E E where
  toFun x := (e (q,x)).2
  invFun y := (e.symm (q,y)).2
  source := {x | (q,x) ∈ e.source}
  target := {y | (q,y) ∈ e.target}
  map_source' x hx := by
    have h := e.map_source hx
    have hw : e (q,x) = (q,(e (q,x)).2) := Prod.ext (he _) rfl
    rwa [hw] at h
  map_target' y hy := by
    have h := e.map_target hy
    have hw : e.symm (q,y) = (q,(e.symm (q,y)).2) :=
      Prod.ext (familyInverse_fst e he hy) rfl
    rwa [hw] at h
  left_inv' x hx := by
    have h := congrArg Prod.snd (e.left_inv hx)
    have hw : e (q,x) = (q,(e (q,x)).2) := Prod.ext (he _) rfl
    rwa [hw] at h
  right_inv' y hy := by
    have h := congrArg Prod.snd (e.right_inv hy)
    have hw : e.symm (q,y) = (q,(e.symm (q,y)).2) :=
      Prod.ext (familyInverse_fst e he hy) rfl
    rwa [hw] at h
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := continuous_snd.continuousOn.comp
    (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => hx)) (fun _ _ => mem_univ _)
  continuousOn_invFun := continuous_snd.continuousOn.comp
    (e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => hx)) (fun _ _ => mem_univ _)
end FiberInverse

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffOn_fiberInverse (e : OpenPartialHomeomorph (P × E) (P × E))
    (he : ∀ w, (e w).1 = w.1) (q : P)
    (hi : ContDiffOn ℝ (∞ : WithTop ℕ∞) e.symm e.target) :
    ContDiffOn ℝ (∞ : WithTop ℕ∞) (fiberOpenPartialHomeomorph e he q).symm
      (fiberOpenPartialHomeomorph e he q).target := by
  exact (hi.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (fun _ hx => hx)).snd
end YauCounterexamples

end

end OAI
