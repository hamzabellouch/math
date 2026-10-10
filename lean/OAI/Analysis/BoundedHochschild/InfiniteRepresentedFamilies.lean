import OAI.Analysis.BoundedHochschild.CompressedAveragingNorms
import OAI.Analysis.BoundedHochschild.InfiniteRepresentedAverages

namespace OAI

/-! Infinite normalized rows preserve the closed represented families used
in the minimal-family argument. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma infinite_represented_average_mem_family
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    (F : Set (H →WOT[ℂ] K)) (hclosed : IsClosed F)
    (hinv : RepresentedRightAverageInvariant π σ F) (W : H →WOT[ℂ] K) (hW : W ∈ F)
    (m : I → M) (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) :
    ContinuousLinearMapWOT.ofCLM (infiniteRepresentedRightAverage π σ m hm W.toCLM) ∈ F := by
  classical
  have ht : Tendsto (fun s : Finset I => weakRepresentedRightAverage π σ (completedRow m s) W)
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM
        (infiniteRepresentedRightAverage π σ m hm W.toCLM))) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro ξ η
    exact tendsto_const_nhds.inner (completedRow_average_tendsto π σ m hm hlim W.toCLM ξ)
  apply hclosed.mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  let q := Fintype.equivFin (Option s)
  let r := completedRow m s
  have hr : ∑ i, r i * star (r i) = 1 := completedRow_normalized m s (hm s)
  have hq : ∑ i, r (q.symm i) * star (r (q.symm i)) = 1 :=
    (q.symm.sum_comp (fun i => r i * star (r i))).trans hr
  have hin := hinv (Fintype.card (Option s)) (r ∘ q.symm) hq hW
  have he := congrArg ContinuousLinearMapWOT.ofCLM
    (representedRightAverage_reindex π σ q.symm r W.toCLM)
  change weakRepresentedRightAverage π σ (r ∘ q.symm) W =
    weakRepresentedRightAverage π σ r W at he
  rwa [he] at hin

end BoundedHochschild.KadisonRingrose

end

end OAI
