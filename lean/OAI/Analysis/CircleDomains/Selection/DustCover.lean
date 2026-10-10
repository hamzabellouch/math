import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

/-!
# Small disjoint neighborhoods of compact dust

A compact totally disconnected subset of a metric space admits finite
open covers with pairwise disjoint closures of arbitrarily small diameter.
-/

open Set Metric TopologicalSpace Filter Function
open scoped Topology

namespace CircleDomainRigidity

theorem exists_small_disjoint_open_cover_of_compact_dust
    {X : Type*} [MetricSpace X] {B : Set X}
    (hB : IsCompact B) (hTD : IsTotallyDisconnected B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (U : Fin n → Set X),
      (∀ i, IsOpen (U i)) ∧ B ⊆ ⋃ i, U i ∧
      Pairwise (Disjoint on fun i => closure (U i)) ∧
      ∀ i, diam (closure (U i)) < ε := by
  classical
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let : TotallyDisconnectedSpace B := totallyDisconnectedSpace_subtype_iff.mpr hTD
  have hcover : IsOpenCover (fun b : B => (⟨ball b (ε / 4), isOpen_ball⟩ : Opens B)) := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro b
    exact mem_iUnion.mpr ⟨b, mem_ball_self (by positivity)⟩
  obtain ⟨n, C, hC, hCov, hDisj⟩ := hcover.exists_finite_nonempty_disjoint_clopen_cover
  let A : Fin n → Set X := fun i => Subtype.val '' (C i : Set B)
  have hAc (i) : IsCompact (A i) := (C i).isClosed.isCompact.image continuous_subtype_val
  have hAd : Pairwise (Disjoint on A) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have heq : v = u := Subtype.ext huv
    subst v
    exact Set.disjoint_left.mp (Clopens.coe_disjoint.mpr (hDisj hij)) hu hv
  have hAn : Pairwise (Disjoint on fun i => 𝓝ˢ (A i)) := by
    intro i j hij
    exact disjoint_nhdsSet_nhdsSet (hAc i).isClosed (hAc j).isClosed (hAd hij)
  obtain ⟨V, hV, hVd⟩ := hAn.exists_mem_filter_basis_of_disjoint
    (fun i => hasBasis_nhdsSet (A i))
  have hsmall (i : Fin n) : ∃ b : B, A i ⊆ ball (b : X) (ε / 4) := by
    obtain ⟨b, hb⟩ := (hC i).2
    refine ⟨b, ?_⟩
    rintro z ⟨u, hu, rfl⟩
    exact hb hu
  choose b hb using hsmall
  have hshrink (i : Fin n) : ∃ U : Set X,
      IsOpen U ∧ A i ⊆ U ∧ closure U ⊆ V i ∩ ball (b i : X) (ε / 4) := by
    apply (hAc i).exists_isOpen_closure_subset
    exact ((hV i).1.inter isOpen_ball).mem_nhdsSet.mpr
      (subset_inter (hV i).2 (hb i))
  choose U hUo hAU hUV using hshrink
  refine ⟨n, U, hUo, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCov (mem_univ (⟨x, hx⟩ : B)))
    exact mem_iUnion.mpr ⟨i, hAU i ⟨⟨x, hx⟩, hi, rfl⟩⟩
  · intro i j hij
    exact (hVd hij).mono (fun _ hx => (hUV i hx).1) (fun _ hx => (hUV j hx).1)
  · intro i
    have hdiam : diam (closure (U i)) ≤ 2 * (ε / 4) :=
      diam_le_of_subset_closedBall (by positivity)
        (fun _ hx => ball_subset_closedBall ((hUV i hx).2))
    linarith

end CircleDomainRigidity

end OAI
