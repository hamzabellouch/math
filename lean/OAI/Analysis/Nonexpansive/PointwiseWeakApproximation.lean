import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace OAI

/-!
# Simultaneous approximation in the pointwise weak topology

A convex family of weak-valued maps can approximate each point in its closure
in norm at any prescribed finite family of arguments.  The finite family is
handled as one vector in the finite product normed space.  Consequently the
chosen approximating map is the same at every argument.

No completeness, reflexivity, or nontriviality assumption is required here.
-/

noncomputable section

open Set
open scoped BigOperators Topology

namespace ReflexiveFixedPoints

universe u v w

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {α : Type v} {ι : Type w}

/-- The underlying normed tuple at a prescribed family of arguments.
This is a linear map, without a claim of weak-to-norm continuity. -/
def finiteNormEvaluation (a : ι → α) :
    (α → WeakSpace ℝ X) →ₗ[ℝ] (ι → X) :=
  LinearMap.pi fun i =>
    (toWeakSpace ℝ X).symm.toLinearMap.comp (LinearMap.proj (a i))

@[simp] theorem finiteNormEvaluation_apply (a : ι → α)
    (f : α → WeakSpace ℝ X) (i : ι) :
    finiteNormEvaluation a f i = (toWeakSpace ℝ X).symm (f (a i)) := rfl

variable [Fintype ι]

/-- Finite evaluation is continuous when its target has the weak topology
of the finite product normed space. -/
theorem continuous_finite_weak_evaluation (a : ι → α) :
    Continuous (fun f : α → WeakSpace ℝ X =>
      toWeakSpace ℝ (ι → X) (finiteNormEvaluation a f)) := by
  classical
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ (ι → X)).flip
  intro φ
  change Continuous (fun f : α → WeakSpace ℝ X => φ (finiteNormEvaluation a f))
  have hdecomp (x : ι → X) :
      φ x = ∑ i,
        (φ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => X) i)) (x i) := by
    change φ x = ∑ i, φ (Pi.single i (x i))
    rw [← map_sum, Finset.univ_sum_single]
  have hc : Continuous (fun f : α → WeakSpace ℝ X =>
      ∑ i, (φ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => X) i))
        (finiteNormEvaluation a f i)) := by
    apply continuous_finsetSum
    intro i _
    exact (WeakBilin.eval_continuous (topDualPairing ℝ X).flip
      (φ.comp (ContinuousLinearMap.single ℝ (fun _ : ι => X) i))).comp
        (continuous_apply (a i))
  simpa only [← hdecomp] using hc

/-- One member of a convex family approximates a point of its pointwise weak
closure simultaneously in norm at every argument in a finite indexed family.
The index type is allowed to be empty, and arguments may repeat. -/
theorem exists_mem_norm_approx_of_mem_pointwiseWeak_closure
    {s : Set (α → WeakSpace ℝ X)} (hs : Convex ℝ s)
    {f : α → WeakSpace ℝ X} (hf : f ∈ closure s)
    (a : ι → α) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ s, ∀ i,
      ‖(toWeakSpace ℝ X).symm (g (a i)) -
        (toWeakSpace ℝ X).symm (f (a i))‖ < ε := by
  let e : (α → WeakSpace ℝ X) →ₗ[ℝ] (ι → X) := finiteNormEvaluation a
  have hconv : Convex ℝ (e '' s) := hs.linear_image e
  have hw : toWeakSpace ℝ (ι → X) (e f) ∈
      closure (toWeakSpace ℝ (ι → X) '' (e '' s)) := by
    rw [Set.image_image]
    exact mem_closure_image (continuous_finite_weak_evaluation a).continuousAt hf
  rw [← hconv.toWeakSpace_closure ℝ] at hw
  obtain ⟨x, hx, hxf⟩ := hw
  have hxf' : x = e f := (toWeakSpace ℝ (ι → X)).injective hxf
  rw [hxf'] at hx
  obtain ⟨y, ⟨g, hg, hgy⟩, hnear⟩ := Metric.mem_closure_iff.1 hx ε hε
  rw [← hgy] at hnear
  refine ⟨g, hg, fun i => ?_⟩
  change ‖e g i - e f i‖ < ε
  rw [← dist_eq_norm]
  exact (dist_le_pi_dist (e g) (e f) i).trans_lt (by
    simpa only [dist_comm] using hnear)

/-- Finset form of simultaneous norm approximation from pointwise weak
closure.  In particular, separate choices at different arguments are not used. -/
theorem exists_mem_norm_approx_finset_of_mem_pointwiseWeak_closure
    {s : Set (α → WeakSpace ℝ X)} (hs : Convex ℝ s)
    {f : α → WeakSpace ℝ X} (hf : f ∈ closure s)
    (t : Finset α) {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ s, ∀ x ∈ t,
      ‖(toWeakSpace ℝ X).symm (g x) -
        (toWeakSpace ℝ X).symm (f x)‖ < ε := by
  classical
  obtain ⟨g, hg, happrox⟩ :=
    exists_mem_norm_approx_of_mem_pointwiseWeak_closure hs hf
      (fun x : t => (x : α)) hε
  exact ⟨g, hg, fun x hx => happrox ⟨x, hx⟩⟩

/-- Simultaneous approximation on every finite set of arguments implies
membership in the product-topology closure.  This uses only the codomain's
pseudometric, so it applies directly to maps taking values in a norm subtype. -/
theorem mem_closure_of_finite_dist_approx
    {Y : Type u} [PseudoMetricSpace Y]
    {B : Set (α → Y)} {f : α → Y}
    (h : ∀ (s : Finset α) (ε : ℝ), 0 < ε →
      ∃ g ∈ B, ∀ a ∈ s, dist (g a) (f a) < ε) :
    f ∈ closure B := by
  classical
  apply mem_closure_iff_nhds.2
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨s, V, hV, hsub⟩ := Filter.mem_pi'.1 hU
  have hVs : Set.pi Set.univ (fun a : s => V a) ∈
      𝓝 (fun a : s => f a) :=
    set_pi_mem_nhds Set.finite_univ (fun a _ => hV a)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hVs
  obtain ⟨g, hg, hdist⟩ := h s ε hε
  refine ⟨g, hsub ?_, hg⟩
  have hgin : (fun a : s => g a) ∈ Set.pi Set.univ (fun a : s => V a) := by
    apply hball
    rw [Metric.mem_ball]
    exact (dist_pi_lt_iff hε).2 fun a => hdist a a.property
  intro a ha
  exact hgin ⟨a, ha⟩ (Set.mem_univ _)

end ReflexiveFixedPoints

end

end OAI
