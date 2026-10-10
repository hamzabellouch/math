import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredTuplePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceBundleBlockPaths

namespace OAI

/-! # Transfer paths of the retained successful states to their image tuples -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {N G W T : Type*} [Group N] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Successful parameters may be correlated. Only their actual reachable
states and paths are used when constructing all image-tuple transitions. -/
theorem reachable_image_tuple_paths
    {h : ℕ} (ι : N →* G) (f : G → G) {Λ : ℝ≥0} (hf : LipschitzWith Λ f)
    (π : G →* Multiplicative W) (x d : G) (initial : N)
    (S : Set (Fin h → N)) (P : T → Prop) (boundary : T → ℕ → N)
    (hzero : ∀ t, P t → boundary t 0 = initial)
    (hreach : ∀ v ∈ S, ∃ t, P t ∧ ∀ i : Fin h, boundary t (i.val + 1) = v i)
    (E : Fin h → Set W) (r L κ B D : ℝ)
    (hpaths : ∀ t, P t → ∀ j : Fin h,
      ∃ γ : Path (x * ι (boundary t j.val) * d) (x * ι (boundary t (j.val + 1)) * d),
        PathMetricBound γ L κ ∧
        (∀ u, ∃ w ∈ E j, ‖(π (f (γ u))).toAdd -
          (π (f (x * ι (boundary t j.val) * d))).toAdd - r • w‖ ≤ B) ∧
        ‖(π (f (x * ι (boundary t (j.val + 1)) * d))).toAdd -
          (π (f (x * ι (boundary t j.val) * d))).toAdd‖ ≤ D) :
    ∀ y ∈ (fun v : Fin h → N => fun i =>
        (f (x * ι initial * d))⁻¹ * f (x * ι (v i) * d)) '' S,
      ∃ paths : ∀ j : Fin h, Path (1 : G)
          ((basedTuplePosition y j.val)⁻¹ * basedTuplePosition y (j.val + 1)),
        (∀ j, PathMetricBound (paths j) (Λ * L) (Λ * κ)) ∧
        (∀ j u, ∃ w ∈ E j, ‖(π (paths j u)).toAdd - r • w‖ ≤ B) ∧
        ∀ j : Fin h,
          ‖(π ((basedTuplePosition y j.val)⁻¹ * basedTuplePosition y (j.val + 1))).toAdd‖ ≤ D := by
  rintro y ⟨v, hv, hy⟩
  obtain ⟨t, ht, hcoords⟩ := hreach v hv
  let vertex := fun j => x * ι (boundary t j) * d
  have heq : (fun i : Fin h => (f (x * ι initial * d))⁻¹ * f (x * ι (v i) * d)) =
      centeredVertexTuple f vertex h := by
    funext i
    dsimp only [centeredVertexTuple, vertex]
    rw [hzero t ht, hcoords i]
  have hy' : y = centeredVertexTuple f vertex h := hy.symm.trans heq
  clear hy heq
  subst y
  choose path hmetric hheight hend using hpaths t ht
  refine ⟨centeredTuplePath f hf.continuous vertex path,
    centeredTuplePath_metric_bound f hf vertex path L κ hmetric,
    centeredTuplePath_height_bound f hf.continuous vertex path π E r B hheight, ?_⟩
  intro j
  rw [centeredVertexTuple_transition, map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [vertex, sub_eq_add_neg, add_comm] using hend j

variable [MeasurableSpace N] [MeasurableMul₂ N] [MeasurableInv N]

/-- Apply the transfer directly to the source-state coordinates produced
by the coupled Haar image theorem. No independent choice of increments
or of their conjugated images is made. -/
theorem source_bundle_image_tuple_paths
    {h : ℕ} (ι : N →* G) (f : G → G) {Λ : ℝ≥0} (hf : LipschitzWith Λ f)
    (π : G →* Multiplicative W) (x d : G) (initial : N)
    (S : Set (Fin h → N)) (P : T → Prop) (products : T → Fin h → N)
    (φ : Fin h → N ≃* N) (ψ : Fin h → N ≃ᵐ N) (hψ : ∀ i z, ψ i z = φ i z)
    (hreach : ∀ v ∈ S, ∃ t, P t ∧ v = sourceBundleStateEquiv h initial ψ (products t))
    (E : Fin h → Set W) (r L κ B D : ℝ)
    (hpaths : ∀ t, P t → ∀ j : Fin h,
      ∃ γ : Path (x * ι (sourceBundleBoundary initial φ (products t) j.val) * d)
          (x * ι (sourceBundleBoundary initial φ (products t) (j.val + 1)) * d),
        PathMetricBound γ L κ ∧
        (∀ u, ∃ w ∈ E j, ‖(π (f (γ u))).toAdd -
          (π (f (x * ι (sourceBundleBoundary initial φ (products t) j.val) * d))).toAdd -
            r • w‖ ≤ B) ∧
        ‖(π (f (x * ι (sourceBundleBoundary initial φ (products t) (j.val + 1)) * d))).toAdd -
          (π (f (x * ι (sourceBundleBoundary initial φ (products t) j.val) * d))).toAdd‖ ≤ D) :
    ∀ y ∈ (fun v : Fin h → N => fun i =>
        (f (x * ι initial * d))⁻¹ * f (x * ι (v i) * d)) '' S,
      ∃ paths : ∀ j : Fin h, Path (1 : G)
          ((basedTuplePosition y j.val)⁻¹ * basedTuplePosition y (j.val + 1)),
        (∀ j, PathMetricBound (paths j) (Λ * L) (Λ * κ)) ∧
        (∀ j u, ∃ w ∈ E j, ‖(π (paths j u)).toAdd - r • w‖ ≤ B) ∧
        ∀ j : Fin h,
          ‖(π ((basedTuplePosition y j.val)⁻¹ * basedTuplePosition y (j.val + 1))).toAdd‖ ≤ D := by
  apply reachable_image_tuple_paths ι f hf π x d initial S P
    (fun t => sourceBundleBoundary initial φ (products t))
    (fun _ _ => sourceBundleBoundary_zero initial φ _) ?_ E r L κ B D hpaths
  intro v hv
  obtain ⟨t, ht, he⟩ := hreach v hv
  refine ⟨t, ht, ?_⟩
  intro i
  rw [he]
  exact sourceBundleBoundary_eq_stateEquiv initial φ ψ hψ (products t) i

end PolycyclicRecognition

end

end OAI
