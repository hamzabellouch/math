import OAI.Analysis.BoundedHochschild.InfiniteAveragingLimits
import OAI.Analysis.BoundedHochschild.MinimalRightAverages

namespace OAI

/-! Closed families invariant under finite normalized averages are also
invariant under every normalized infinite row for which an operator
factorization is given. This justifies the infinite rows in the minimal-family
argument without strengthening its invariance hypothesis. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {I K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem infinite_average_mem_invariant_family (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : Set (M → WeakDual ℂ X)) (hclosed : IsClosed F) (hinv : RightAverageInvariant e F)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M) (hmem : weakOperatorImage e T ∈ F)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (m : I → M) (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, m i * star (m i)) atTop 1) :
    ∃ S : M →L[ℂ] M, ‖S‖ ≤ ‖L‖ * ‖W‖ ∧ weakOperatorImage e S ∈ F ∧
      ∀ a, PredualTendsto e (fun s : Finset I => finiteRightAverage (completedRow m s) T a)
        atTop (S a) := by
  classical
  obtain ⟨S, hn, hconv, _⟩ := exists_infinite_right_average e π L W T hT m hm hlim
  refine ⟨S, hn, ?_, hconv⟩
  have ht : Tendsto (fun s : Finset I => weakOperatorImage e (finiteRightAverage (completedRow m s) T))
      atTop (𝓝 (weakOperatorImage e S)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    exact tendsto_iff_forall_eval_tendsto_topDualPairing.mpr (hconv a)
  apply hclosed.mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  let r := completedRow m s
  let q := Fintype.equivFin (Option s)
  have hr : ∑ j, r j * star (r j) = 1 := completedRow_normalized m s (hm s)
  have hq : ∑ j, r (q.symm j) * star (r (q.symm j)) = 1 :=
    (q.symm.sum_comp (fun j => r j * star (r j))).trans hr
  have hin := hinv (Fintype.card (Option s)) (r ∘ q.symm) hq hmem
  rw [weakRightAverage_image] at hin
  have he := finiteRightAverage_reindex q.symm r T
  change finiteRightAverage (r ∘ q.symm) T = finiteRightAverage r T at he
  rwa [he] at hin

end BoundedHochschild.KadisonRingrose

end

end OAI
