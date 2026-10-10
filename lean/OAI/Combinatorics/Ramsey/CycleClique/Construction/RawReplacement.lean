import OAI.Combinatorics.Ramsey.CycleClique.Construction.RawPathSystem

namespace OAI

/-! Cut two different chains before their representatives and reconnect
through a new outside path, retaining every old vertex. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem amount_union (S T : RawPathSystem G Q) {J : List V}
    (hverts : T.vertices = S.vertices ∪ J.toFinset)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q)
    (hdis : J.Disjoint S.chains.flatten) :
    T.amount = S.amount + J.length := by
  classical
  have hJdiff : J.toFinset \ Q = J.toFinset := by
    apply Finset.sdiff_eq_self_iff_disjoint.mpr
    apply Finset.disjoint_left.mpr
    intro v hv hvQ
    exact hJQ v (List.mem_toFinset.mp hv) hvQ
  have hdisfin : Disjoint (S.vertices \ Q) J.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hv hvJ
    exact List.disjoint_left.mp hdis (List.mem_toFinset.mp hvJ)
      (List.mem_toFinset.mp (Finset.mem_sdiff.mp hv).1)
  unfold amount
  rw [hverts, Finset.union_sdiff_distrib, hJdiff,
    Finset.card_union_of_disjoint hdisfin, List.toFinset_card_of_nodup hJ]

theorem replace_different_chains (S : RawPathSystem G Q)
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q,
      T.chains = P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length := by
  classical
  let merged := B.reverse ++ x :: (J ++ y :: D)
  let K := P ++ A :: M ++ C :: merged :: R
  have hold₁ : A ++ x :: B ∈ S.chains := by simp [hsys]
  have hold₂ : C ++ y :: D ∈ S.chains := by simp [hsys]
  have hremain : ∀ l, l ∈ P ∨ l ∈ M ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  have hp : K.flatten.Perm (S.chains.flatten ++ J) := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [K, merged, hsys, List.flatten_append, List.flatten_cons,
      List.count_append, List.count_cons, List.count_reverse]
    omega
  have hflat : K.flatten.Nodup := hp.nodup_iff.mpr
    (S.flatten_nodup.append hJ hdis.symm)
  have hpaths₁ := List.isChain_append.mp (S.paths _ hold₁).2
  have hpaths₂ := List.isChain_append.mp (S.paths _ hold₂).2
  have hsteps₁ := List.isChain_append.mp (S.no_clique_steps _ hold₁)
  have hsteps₂ := List.isChain_append.mp (S.no_clique_steps _ hold₂)
  have hmerged : merged.IsChain G.Adj :=
    reverse_join_chain (fun _ _ h => h.symm) hpaths₁.2.1 hpaths₂.2.1 hpath
  have hmergedSteps : merged.IsChain (fun a b => ¬ (a ∈ Q ∧ b ∈ Q)) :=
    reverse_join_chain (fun _ _ h h' => h h'.symm) hsteps₁.2.1 hsteps₂.2.1
      (chain_outside_interior_of_ne_nil hJpos hJQ)
  have hmergedEq : merged = (x :: B).reverse ++ J ++ (y :: D) := by
    simp [merged, List.append_assoc]
  have hhead : merged.head? = (x :: B).getLast? := by
    rw [hmergedEq, List.append_assoc,
      List.head?_append_of_ne_nil _ (by simp), List.head?_reverse]
  have hlast : merged.getLast? = (y :: D).getLast? := by
    rw [hmergedEq]
    have hyD := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
    simp only [List.getLast?_append, hyD, Option.or]
  let T : RawPathSystem G Q := {
    chains := K
    paths := by
      intro l hl
      refine ⟨(List.nodup_flatten.mp hflat).1 l hl, ?_⟩
      simp only [K, List.mem_append, List.mem_cons, or_assoc] at hl
      rcases hl with hl | rfl | hl | rfl | rfl | hl
      · exact (S.paths l (hremain l (Or.inl hl))).2
      · exact hpaths₁.1
      · exact (S.paths l (hremain l (Or.inr (Or.inl hl)))).2
      · exact hpaths₂.1
      · exact hmerged
      · exact (S.paths l (hremain l (Or.inr (Or.inr hl)))).2
    disjoint := (List.nodup_flatten.mp hflat).2
    endpoints := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons, or_assoc] at hl
      rcases hl with hl | rfl | hl | rfl | rfl | hl
      · exact S.endpoints l (hremain l (Or.inl hl))
      · refine ⟨?_, hA⟩
        intro v hv
        exact (S.endpoints _ hold₁).1 v (List.mem_head?_append_of_mem_head? hv)
      · exact S.endpoints l (hremain l (Or.inr (Or.inl hl)))
      · refine ⟨?_, hC⟩
        intro v hv
        exact (S.endpoints _ hold₂).1 v (List.mem_head?_append_of_mem_head? hv)
      · constructor
        · intro v hv
          rw [hhead] at hv
          apply (S.endpoints _ hold₁).2 v
          have hs := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
          simpa only [List.getLast?_append, hs, Option.or] using hv
        · intro v hv
          rw [hlast] at hv
          apply (S.endpoints _ hold₂).2 v
          have hs := List.getLast?_eq_some_getLast (show y :: D ≠ [] by simp)
          simpa only [List.getLast?_append, hs, Option.or] using hv
      · exact S.endpoints l (hremain l (Or.inr (Or.inr hl)))
    no_clique_steps := by
      intro l hl
      simp only [K, List.mem_append, List.mem_cons, or_assoc] at hl
      rcases hl with hl | rfl | hl | rfl | rfl | hl
      · exact S.no_clique_steps l (hremain l (Or.inl hl))
      · exact hsteps₁.1
      · exact S.no_clique_steps l (hremain l (Or.inr (Or.inl hl)))
      · exact hsteps₂.1
      · exact hmergedSteps
      · exact S.no_clique_steps l (hremain l (Or.inr (Or.inr hl))) }
  refine ⟨T, rfl, amount_union S T ?_ hJ hJQ hdis⟩
  ext v
  change v ∈ K.flatten.toFinset ↔ v ∈ S.chains.flatten.toFinset ∪ J.toFinset
  simp only [List.mem_toFinset, Finset.mem_union, ← List.mem_append]
  exact hp.mem_iff

theorem different_chain_count {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hD : ∀ v ∈ (y :: D).getLast?, v ∈ Q)
    (hJQ : ∀ z ∈ J, z ∉ Q) :
    rawAssignedCount Q (P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R) +
        (if A = [] then 0 else 1) + (if C = [] then 0 else 1) =
      rawAssignedCount Q (P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R) + 1 := by
  have hBpos := chainCliqueCount_pos_last (show x :: B ≠ [] by simp) hB
  have hDpos := chainCliqueCount_pos_last (show y :: D ≠ [] by simp) hD
  have hJzero := chainCliqueCount_eq_zero hJQ
  have heq : B.reverse ++ x :: (J ++ y :: D) =
      (x :: B).reverse ++ J ++ (y :: D) := by simp [List.append_assoc]
  rw [heq]
  simp only [rawAssignedCount, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons, chainCliqueCount_append, chainCliqueCount_reverse, hJzero,
    Nat.add_zero]
  have hnil : chainCliqueCount Q ([] : List V) = 0 := rfl
  by_cases ha : A = []
  · by_cases hc : C = []
    · simp only [ha, hc, ↓reduceIte, hnil]
      omega
    · have hCpos := chainCliqueCount_pos_last hc hC
      simp only [ha, hc, ↓reduceIte, hnil]
      omega
  · have hApos := chainCliqueCount_pos_last ha hA
    by_cases hc : C = []
    · simp only [ha, hc, ↓reduceIte, hnil]
      omega
    · have hCpos := chainCliqueCount_pos_last hc hC
      simp only [ha, hc, ↓reduceIte]
      omega

end CycleClique.Construction.RawPathSystem

end OAI
