import OAI.Probability.FreeIsing.Estimates.FiniteComponentGeometry
import OAI.Probability.FreeIsing.Estimates.FiniteIsingSplit

namespace OAI

noncomputable section

namespace Problem367.FiniteIsingSplit

variable {d : ℕ}

lemma field_congr_domain (beta : ℝ) {D E : Finset (TreeVertex d)}
    (h : D = E) (v : D) (w : E) (hv : v.1 = w.1)
    (y : TreeVertex d → ℝ) : field beta D v y = field beta E w y := by
  subst E
  have hw : v = w := Subtype.ext hv
  subst w
  rfl

theorem cavityFromSites_root_component {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (field beta D ⟨ConnectedHull.root d, hroot⟩ y,
        field beta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y) =
      (field beta (rootComplementFinset D c)
          ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩ y,
        field beta (rootComponentFinset D c)
          ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y) := by
  classical
  let A := rootComplementFinset D c
  let B := rootComponentFinset D c
  let u : A := ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩
  let v : B := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hAB : Disjoint A B := (rootComponentFinset_disjoint_complement D c).symm
  have hUnion : A ∪ B = D := by
    rw [Finset.union_comm]
    exact rootComponentFinset_union_complement D c
  have hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B) := by
    rw [hUnion, inducedEdges_rootComponent_split hroot c hc]
    congr 1
    exact Finset.union_comm _ _
  have h := cavityFromSites_eq_component_fields hbeta A B hAB u v hEdges y
  have hu := field_congr_domain beta hUnion
    (⟨u, Finset.mem_union_left B u.property⟩ : ↥(A ∪ B))
    ⟨ConnectedHull.root d, hroot⟩ rfl y
  have hv := field_congr_domain beta hUnion
    (⟨v, Finset.mem_union_right A v.property⟩ : ↥(A ∪ B))
    ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ rfl y
  rw [hu, hv] at h
  exact h

theorem field_root_eq_components (beta : ℝ)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    field beta D ⟨ConnectedHull.root d, hroot⟩ y =
      field beta (rootComplementFinset D c)
        ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩ y +
      cavityMessage (Real.tanh beta) (field beta (rootComponentFinset D c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y) := by
  classical
  let A := rootComplementFinset D c
  let B := rootComponentFinset D c
  let u : A := ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩
  let v : B := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hAB : Disjoint A B := (rootComponentFinset_disjoint_complement D c).symm
  have hUnion : A ∪ B = D := by
    rw [Finset.union_comm]
    exact rootComponentFinset_union_complement D c
  have hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B) := by
    rw [hUnion, inducedEdges_rootComponent_split hroot c hc]
    congr 1
    exact Finset.union_comm _ _
  have h := field_union_fst beta A B hAB u v hEdges y
  have hu := field_congr_domain beta hUnion
    (⟨u, Finset.mem_union_left B u.property⟩ : ↥(A ∪ B))
    ⟨ConnectedHull.root d, hroot⟩ rfl y
  rw [hu] at h
  exact h

end Problem367.FiniteIsingSplit

end

end OAI
