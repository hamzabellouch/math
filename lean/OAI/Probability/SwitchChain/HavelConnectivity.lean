import OAI.Probability.SwitchChain.HavelInduction
import OAI.Probability.SwitchChain.FrozenRows
import OAI.Probability.SwitchChain.SwitchWitness
import OAI.Probability.SwitchChain.NeighborAlignment

namespace OAI

noncomputable section

namespace Problem315
attribute [local instance] Classical.propDecidable

theorem havel_neighborhood_repair_of_moves {n : Nat} {d : Fin n → Nat}
    (r : GraphState n d → GraphState n d → Prop)
    (hmoves : ∀ (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e),
      G.val.Adj a b → G.val.Adj c e → ¬ G.val.Adj a c → ¬ G.val.Adj b e →
      r G (fourVertexState G a b c e h))
    (R T : Finset (Fin n)) (v : Fin n) (G : GraphState n d)
    (hv : v ∈ R) (hTR : T ⊆ R.erase v)
    (hsize : T.card = (R.filter (G.val.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.val.Adj i)).card ≤ (R.filter (G.val.Adj j)).card) :
    ∃ H : GraphState n d, Relation.ReflTransGen r G H ∧
      HavelCanonical.AgreeOutside R G.val H.val ∧ R.filter (H.val.Adj v) = T := by
  classical
  let A := {H : GraphState n d // FrozenRowsAgree H.val G.val R}
  let rA : A → A → Prop := fun H K => r H.val K.val
  let N : A → Finset (Fin n) := fun H => R.filter (H.val.val.Adj v)
  have hres (H : A) (w : Fin n) :
      (R.filter (H.val.val.Adj w)).card = (R.filter (G.val.Adj w)).card :=
    graphState_residualDegree_eq H.val G R H.property w
  have hcard (H : A) : (N H).card = T.card := (hres H v).trans hsize.symm
  have hstep : ∀ H i j, i ∈ N H → i ∉ T → j ∈ T → j ∉ N H →
      ∃ K, rA H K ∧ N K = insert j ((N H).erase i) := by
    intro H i j hi hiT hjT hj
    obtain ⟨hiR, hvi⟩ := Finset.mem_filter.mp hi
    have hjR : j ∈ R := Finset.mem_of_mem_erase (hTR hjT)
    have hvj_ne : v ≠ j := (Finset.mem_erase.mp (hTR hjT)).1.symm
    have hvj : ¬ H.val.val.Adj v j := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨hjR, h⟩)
    have hdeg : (R.filter (H.val.val.Adj i)).card ≤
        (R.filter (H.val.val.Adj j)).card := by
      rw [hres H i, hres H j]
      exact hsorted i hiR hvi.ne.symm hiT j hjT
    obtain ⟨k, hkR, hkv, hki, hkj, hjk, hik⟩ :=
      Havel.exists_switch_witness_in H.val.val R hv hiR hjR hvi hvj hvj_ne hdeg
    have hij : i ≠ j := by
      intro heq
      exact hiT (heq ▸ hjT)
    have hdist : FourDistinct v i j k :=
      ⟨hvi.ne, hvj_ne, hkv.symm, hij, hki.symm, hkj.symm⟩
    let K := fourVertexState H.val v i j k hdist
    have hfreeze : FrozenRowsAgree K.val H.val.val R :=
      fourVertexState_frozenRows H.val R v i j k hdist hv hiR hjR hkR hvi hjk hvj hik
    let KA : A := ⟨K, hfreeze.trans H.property⟩
    refine ⟨KA, hmoves H.val v i j k hdist hvi hjk hvj hik, ?_⟩
    exact fourVertexState_residual_neighbors H.val R v i j k hdist hjR hvi hjk hvj hik
  let GA : A := ⟨G, FrozenRowsAgree.refl G.val R⟩
  obtain ⟨H, hpath, hneigh⟩ := reach_target_by_neighbor_swaps rA N T hcard hstep GA
  refine ⟨H.val, ?_, ?_, hneigh⟩
  · exact Relation.ReflTransGen.lift (fun K : A => K.val) (fun _ _ h => h) _ _ hpath
  · intro u hu w
    exact (H.property u hu w).symm

theorem havel_neighborhood_repair {n : Nat} {d : Fin n → Nat}
    (R T : Finset (Fin n)) (v : Fin n) (G : GraphState n d)
    (hv : v ∈ R) (hTR : T ⊆ R.erase v)
    (hsize : T.card = (R.filter (G.val.Adj v)).card)
    (hsorted : ∀ i ∈ R, i ≠ v → i ∉ T → ∀ j ∈ T,
      (R.filter (G.val.Adj i)).card ≤ (R.filter (G.val.Adj j)).card) :
    ∃ H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H ∧
      HavelCanonical.AgreeOutside R G.val H.val ∧ R.filter (H.val.Adj v) = T :=
  havel_neighborhood_repair_of_moves (SwitchStep n d) switchStep_fourVertexState
    R T v G hv hTR hsize hsorted

private theorem graphDegree_eq_degree {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) : graphDegree G v = G.degree v := by
  classical
  unfold graphDegree SimpleGraph.degree
  congr 1
  ext w
  simp

theorem connectivity_of_fourVertex_moves (n : Nat) (d : Fin n → Nat)
    (r : GraphState n d → GraphState n d → Prop)
    (hsymm : ∀ ⦃first second⦄, r first second → r second first)
    (hmoves : ∀ (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e),
      G.val.Adj a b → G.val.Adj c e → ¬ G.val.Adj a c → ¬ G.val.Adj b e →
      r G (fourVertexState G a b c e h))
    (G H : GraphState n d) : Relation.ReflTransGen r G H := by
  classical
  apply HavelCanonical.connected_of_neighborhood_repair
    (fun K : GraphState n d => K.val) Subtype.val_injective r hsymm _ _ G H
  · intro K L v
    rw [← graphDegree_eq_degree, ← graphDegree_eq_degree]
    exact (K.property v).trans (L.property v).symm
  · intro R T v K hv hTR hsize hsorted
    exact havel_neighborhood_repair_of_moves r hmoves R T v K hv hTR hsize hsorted

theorem switch_connectivity_direct (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : Relation.ReflTransGen (SwitchStep n d) G H :=
  connectivity_of_fourVertex_moves n d (SwitchStep n d) (fun _ _ h => switchStep_symm h)
    switchStep_fourVertexState G H

end Problem315

end

end OAI
