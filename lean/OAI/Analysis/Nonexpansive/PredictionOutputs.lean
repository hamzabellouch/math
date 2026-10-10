import OAI.Analysis.Nonexpansive.Basic
import OAI.Analysis.Nonexpansive.TreeEvaluation
import OAI.Analysis.Nonexpansive.PredictionCompact

namespace OAI

/-!
# Actual evaluated prediction outputs and their compact detector sets

At a candidate one level below a completed cutoff, the parent residual inputs
are formed from the earlier candidate labels. The parent maps and the prior
tree evaluation are then applied in the stated order. Compactness chooses weak
limits of these already evaluated outputs. Uniform coefficient estimates give
norm continuity of their image without weak continuity of a nonlinear map.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace ReflexiveFixedPoints.Prediction

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Actual existence of a weak ultrafilter limit in a weakly compact set. -/
theorem exists_weakLimit {J : Type*} {K : Set X} (hK : WeaklyCompact K)
    (q : J → K) (U : Ultrafilter J) :
    ∃ z : K, Tendsto (fun j => toWeakSpace ℝ X (q j : X)) (U : Filter J)
      (𝓝 (toWeakSpace ℝ X (z : X))) := by
  let f : J → WeakSpace ℝ X := fun j => toWeakSpace ℝ X (q j : X)
  have hmem : (toWeakSpace ℝ X) '' K ∈ Ultrafilter.map f U := by
    rw [Ultrafilter.mem_map]
    exact Filter.univ_mem' fun j => ⟨(q j : X), (q j).property, rfl⟩
  obtain ⟨z, hzK, hz⟩ :=
    (show IsCompact ((toWeakSpace ℝ X) '' K) from hK).ultrafilter_le_nhds'
      (Ultrafilter.map f U) hmem
  obtain ⟨x, hx, hxeq⟩ := hzK
  refine ⟨⟨x, hx⟩, ?_⟩
  change Filter.map f (U : Filter J) ≤ 𝓝 (toWeakSpace ℝ X x)
  rw [hxeq]
  exact hz

/-- A chosen actual limit, obtained from compactness rather than a limit-existence field. -/
def chosenWeakLimit {J : Type*} {K : Set X} (hK : WeaklyCompact K)
    (q : J → K) (U : Ultrafilter J) : K :=
  Classical.choose (exists_weakLimit hK q U)

theorem tendsto_chosenWeakLimit {J : Type*} {K : Set X} (hK : WeaklyCompact K)
    (q : J → K) (U : Ultrafilter J) :
    Tendsto (fun j => toWeakSpace ℝ X (q j : X)) (U : Filter J)
      (𝓝 (toWeakSpace ℝ X (chosenWeakLimit hK q U : X))) :=
  Classical.choose_spec (exists_weakLimit hK q U)

section TreePredictions

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K) (k : ℕ)
variable {I : Type*} [Fintype I]
variable (parent : I → T.Node k) (y : I → K)

/-- The common point receives all unassigned mass in each parent group. -/
def residualInput (b : K) (theta : coefficientSet parent) (p : T.Node k) : K :=
  ⟨residualPoint parent (fun i => (y i : X)) (b : X) theta.val p,
    residualPoint_mem parent E.convex (fun i => (y i : X))
      (fun i => (y i).property) (b : X) b.property theta.property p⟩

@[simp] theorem residualInput_val (b : K) (theta : coefficientSet parent)
    (p : T.Node k) :
    (residualInput E k parent y b theta p : X) =
      residualPoint parent (fun i => (y i : X)) (b : X) theta.val p := rfl

/-- Apply the parent maps once, then the actual evaluation strictly above the cutoff. -/
def evaluatedPrediction (b : K) (theta : coefficientSet parent) : K :=
  E.evaluate k (fun p => E.map k p (residualInput E k parent y b theta p))

/-- Uniform coefficient control of the actual nonlinear root evaluation. -/
theorem evaluatedPrediction_norm_sub_le
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (b : K) (theta eta : coefficientSet parent) :
    ‖(evaluatedPrediction E k parent y b theta : X) -
      evaluatedPrediction E k parent y b eta‖ ≤
        ∑ i, |theta.val i - eta.val i| := by
  unfold evaluatedPrediction
  apply E.evaluate_norm_sub_le_of_forall
  intro p
  have hm :
      ‖(E.map k p (residualInput E k parent y b theta p) : X) -
        E.map k p (residualInput E k parent y b eta p)‖ ≤
      ‖(residualInput E k parent y b theta p : X) -
        residualInput E k parent y b eta p‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using (E.nonexpansive k p).dist_le_mul
        (residualInput E k parent y b theta p) (residualInput E k parent y b eta p)
  refine hm.trans ?_
  exact residualPoint_norm_sub_le parent
    (fun a ha b hb => hdiam ⟨a, ha⟩ ⟨b, hb⟩)
    (fun i => (y i : X)) (fun i => (y i).property)
    (b : X) b.property theta.val eta.val p

/-- The actual weak limit of already evaluated prediction outputs. -/
def predictionWeakLimit (hK : WeaklyCompact K) (b : ℕ → K) (U : Ultrafilter ℕ)
    (theta : coefficientSet parent) : K :=
  chosenWeakLimit hK (fun j => evaluatedPrediction E k parent y (b j) theta) U

theorem tendsto_predictionWeakLimit (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (theta : coefficientSet parent) :
    Tendsto (fun j => toWeakSpace ℝ X
      (evaluatedPrediction E k parent y (b j) theta : X)) (U : Filter ℕ)
      (𝓝 (toWeakSpace ℝ X (predictionWeakLimit E k parent y hK b U theta : X))) :=
  tendsto_chosenWeakLimit hK
    (fun j => evaluatedPrediction E k parent y (b j) theta) U

/-- The chosen weak limits satisfy the same uniform sum-norm coefficient estimate. -/
theorem predictionWeakLimit_norm_sub_le (hK : WeaklyCompact K)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (b : ℕ → K) (U : Ultrafilter ℕ) (theta eta : coefficientSet parent) :
    ‖(predictionWeakLimit E k parent y hK b U theta : X) -
      predictionWeakLimit E k parent y hK b U eta‖ ≤
        ∑ i, |theta.val i - eta.val i| :=
  norm_sub_le_of_weak_tendsto
    (tendsto_predictionWeakLimit E k parent y hK b U theta)
    (tendsto_predictionWeakLimit E k parent y hK b U eta)
    (fun j => evaluatedPrediction_norm_sub_le E k parent y hdiam (b j) theta eta)

/-- Norm continuity in the original ambient norm, after choosing the weak limits. -/
theorem continuous_predictionWeakLimit_val (hK : WeaklyCompact K)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (b : ℕ → K) (U : Ultrafilter ℕ) :
    Continuous (fun theta => (predictionWeakLimit E k parent y hK b U theta : X)) :=
  continuous_of_coefficient_bound _
    (predictionWeakLimit_norm_sub_le E k parent y hK hdiam b U)

/-- The limit map is also continuous into the literal norm subtype. -/
theorem continuous_predictionWeakLimit (hK : WeaklyCompact K)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (b : ℕ → K) (U : Ultrafilter ℕ) :
    Continuous (predictionWeakLimit E k parent y hK b U) :=
  (continuous_predictionWeakLimit_val E k parent y hK hdiam b U).subtype_mk
    (fun theta => (predictionWeakLimit E k parent y hK b U theta).property)

/-- The image of the actual prediction limits is norm compact. -/
theorem isCompact_predictionWeakLimit_range (hK : WeaklyCompact K)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (b : ℕ → K) (U : Ultrafilter ℕ) :
    IsCompact (Set.range (fun theta =>
      (predictionWeakLimit E k parent y hK b U theta : X))) := by
  let : CompactSpace (coefficientSet parent) :=
    isCompact_iff_compactSpace.mp (isCompact_coefficientSet parent)
  exact isCompact_range (continuous_predictionWeakLimit_val E k parent y hK hdiam b U)

/-- The first `k + 1` test points and every possible actual prediction limit.
The sequence is supplied before the candidate map; density is only used later. -/
def detectorSet (hK : WeaklyCompact K) (b : ℕ → K) (U : Ultrafilter ℕ)
    (densePoints : ℕ → K) : Set X :=
  Set.range (fun i : Fin (k + 1) => (densePoints i.val : X)) ∪
    Set.range (fun theta => (predictionWeakLimit E k parent y hK b U theta : X))

/-- A test point witnesses nonemptiness before any current candidate is chosen. -/
theorem detectorSet_nonempty (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (densePoints : ℕ → K) :
    (detectorSet E k parent y hK b U densePoints).Nonempty := by
  refine ⟨(densePoints 0 : X), Or.inl ?_⟩
  exact ⟨⟨0, Nat.succ_pos k⟩, rfl⟩

/-- Both parts of the detector set consist of actual points of `K`. -/
theorem detectorSet_subset (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (densePoints : ℕ → K) :
    detectorSet E k parent y hK b U densePoints ⊆ K := by
  intro x hx
  rcases hx with ⟨i, rfl⟩ | ⟨theta, rfl⟩
  · exact (densePoints i.val).property
  · exact (predictionWeakLimit E k parent y hK b U theta).property

theorem mem_detectorSet_prefix (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (densePoints : ℕ → K) (i : Fin (k + 1)) :
    (densePoints i.val : X) ∈ detectorSet E k parent y hK b U densePoints :=
  Or.inl ⟨i, rfl⟩

theorem mem_detectorSet_predictionWeakLimit (hK : WeaklyCompact K) (b : ℕ → K)
    (U : Ultrafilter ℕ) (densePoints : ℕ → K) (theta : coefficientSet parent) :
    (predictionWeakLimit E k parent y hK b U theta : X) ∈
      detectorSet E k parent y hK b U densePoints :=
  Or.inr ⟨theta, rfl⟩

/-- This compactness is in the original norm topology, as required by the detector lemma. -/
theorem isCompact_detectorSet (hK : WeaklyCompact K)
    (hdiam : ∀ a b : K, ‖(a : X) - (b : X)‖ ≤ 1)
    (b : ℕ → K) (U : Ultrafilter ℕ) (densePoints : ℕ → K) :
    IsCompact (detectorSet E k parent y hK b U densePoints) :=
  (Set.finite_range (fun i : Fin (k + 1) => (densePoints i.val : X))).isCompact.union
    (isCompact_predictionWeakLimit_range E k parent y hK hdiam b U)

end TreePredictions

end ReflexiveFixedPoints.Prediction

end

end OAI
