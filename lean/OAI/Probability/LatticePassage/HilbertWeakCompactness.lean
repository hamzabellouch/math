import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

namespace CompanionFPP
open Topology Filter Metric Bornology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma hilbert_bidual_surjective : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) := by
  intro F
  let g : StrongDual ℝ H := F.comp (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ H).symm g, ?_⟩
  ext l
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ H).surjective l
  change inner ℝ y ((InnerProductSpace.toDual ℝ H).symm g) = g y
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

omit [CompleteSpace H] in

lemma isClosed_weakImage {s : Set H} (hc : Convex ℝ s) (hs : IsClosed s) :
    IsClosed (toWeakSpace ℝ H '' s) := by
  rw [← closure_eq_iff_isClosed, ← hc.toWeakSpace_closure ℝ, hs.closure_eq]

theorem hilbert_isCompact_weak_closedBall (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' closedBall (0 : H) r) := by
  have hc := NormedSpace.isCompact_closure_of_isBounded ℝ H
    (toWeakSpace ℝ H '' closedBall (0 : H) r) (by
      simpa only [Set.preimage_image_eq _ (toWeakSpace ℝ H).injective] using
        (isBounded_closedBall (x := (0 : H)) (r := r))) (by
      intro x _
      obtain ⟨y, hy⟩ := hilbert_bidual_surjective (H := H) (WeakDual.toStrongDual x)
      refine ⟨toWeakSpace ℝ H y, ?_⟩
      exact hy)
  rwa [(isClosed_weakImage (convex_closedBall (0 : H) r) isClosed_closedBall).closure_eq] at hc

theorem exists_weak_product_limit {I : Type*} (f : ℕ → I → H) (R : I → ℝ)
    (hb : ∀ n i, ‖f n i‖ ≤ R i) :
    ∃ (u : I → WeakSpace ℝ H) (l : Filter ℕ), l.NeBot ∧ l ≤ atTop ∧
      Tendsto (fun n i => toWeakSpace ℝ H (f n i)) l (𝓝 u) := by
  have hc : IsCompact {x : I → WeakSpace ℝ H | ∀ i, x i ∈ toWeakSpace ℝ H '' closedBall (0 : H) (R i)} :=
    isCompact_pi_infinite (fun i => hilbert_isCompact_weak_closedBall (H := H) (R i))
  obtain ⟨u, _, hu⟩ := hc.exists_mapClusterPt (f := atTop)
    (u := fun n i => toWeakSpace ℝ H (f n i)) (le_principal_iff.mpr (by
      change ∀ᶠ n : ℕ in atTop, ∀ i, toWeakSpace ℝ H (f n i) ∈ _
      exact Eventually.of_forall (fun n i => ⟨f n i, mem_closedBall_zero_iff.mpr (hb n i), rfl⟩)))
  exact ⟨u, atTop ⊓ comap (fun n i => toWeakSpace ℝ H (f n i)) (𝓝 u),
    (by simpa only [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, inf_comm] using hu), inf_le_left, tendsto_iff_comap.mpr inf_le_right⟩

end CompanionFPP

end OAI
