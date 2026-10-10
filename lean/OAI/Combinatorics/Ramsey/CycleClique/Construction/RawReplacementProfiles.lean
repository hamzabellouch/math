import OAI.Combinatorics.Ramsey.CycleClique.Construction.ReplacementProfiles
import OAI.Combinatorics.Ramsey.CycleClique.Construction.SameChainReplacement

namespace OAI

/-! Assigned-amount bookkeeping for the two actual representative surgeries. -/

namespace CycleClique.Construction.RawPathSystem

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} {Q : Finset V}

theorem exists_subchain_profile (S : RawPathSystem G Q) (C : List (List V))
    (hC : ∀ l ∈ C, l ∈ S.chains) :
    ∃ w, SystemAssignedAmounts Q C w := by
  obtain ⟨P, hP⟩ := exists_chain_profiles C
    (fun l hl => S.endpoints l (hC l hl))
    (fun l hl => S.no_clique_steps l (hC l hl))
  exact ⟨P.flatten, SystemAssignedAmounts.of_profiles hP⟩

theorem replacement_profiles_different (S T : RawPathSystem G Q)
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (htsys : T.chains = P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  have hmem₁ : A ++ x :: B ∈ S.chains := by simp [hsys]
  have hmem₂ : C ++ y :: D ∈ S.chains := by simp [hsys]
  obtain ⟨X⟩ := exists_assigned_cut_profile (S.endpoints _ hmem₁)
    (S.no_clique_steps _ hmem₁) hA
  obtain ⟨Y⟩ := exists_assigned_cut_profile (S.endpoints _ hmem₂)
    (S.no_clique_steps _ hmem₂) hC
  have hremain : ∀ l, l ∈ P ∨ l ∈ M ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  obtain ⟨wp, hp⟩ := S.exists_subchain_profile P (fun l hl => hremain l (Or.inl hl))
  obtain ⟨wm, hm⟩ := S.exists_subchain_profile M (fun l hl => hremain l (Or.inr (Or.inl hl)))
  obtain ⟨wr, hr⟩ := S.exists_subchain_profile R (fun l hl => hremain l (Or.inr (Or.inr hl)))
  obtain ⟨original, output, kept, removed, ho, ht, hop, htp⟩ :=
    different_chain_profiles X Y hp hm hr hJ hJne
  exact ⟨original, output, kept, removed, hsys.symm ▸ ho, htsys.symm ▸ ht, hop, htp⟩

theorem replacement_profiles_same (S T : RawPathSystem G Q)
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (htsys : T.chains = P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  have hmem : A ++ (x :: B) ++ y :: D ∈ S.chains := by simp [hsys]
  have hprefixEnd : ∀ v ∈ (A ++ x :: B).getLast?, v ∈ Q := by
    intro v hv
    apply hB v
    have he := List.getLast?_eq_some_getLast (show x :: B ≠ [] by simp)
    simpa only [List.getLast?_append, he, Option.or] using hv
  have hprefixEnds : (∀ v ∈ (A ++ x :: B).head?, v ∈ Q) ∧
      (∀ v ∈ (A ++ x :: B).getLast?, v ∈ Q) := by
    refine ⟨?_, hprefixEnd⟩
    intro v hv
    exact (S.endpoints _ hmem).1 v (List.mem_head?_append_of_mem_head? hv)
  have hprefixSteps : (A ++ x :: B).IsChain (fun u v => ¬ (u ∈ Q ∧ v ∈ Q)) :=
    (List.isChain_append.mp (S.no_clique_steps _ hmem)).1
  obtain ⟨X⟩ := exists_assigned_cut_profile hprefixEnds hprefixSteps hA
  obtain ⟨Y⟩ := exists_assigned_cut_profile (S.endpoints _ hmem)
    (S.no_clique_steps _ hmem) hprefixEnd
  have hremain : ∀ l, l ∈ P ∨ l ∈ R → l ∈ S.chains := by
    intro l hl
    simp only [hsys, List.mem_append, List.mem_cons]
    tauto
  obtain ⟨wp, hp⟩ := S.exists_subchain_profile P (fun l hl => hremain l (Or.inl hl))
  obtain ⟨wr, hr⟩ := S.exists_subchain_profile R (fun l hl => hremain l (Or.inr hl))
  obtain ⟨original, output, kept, removed, ho, ht, hop, htp⟩ :=
    same_chain_profiles X Y hp hr hJ hJne
  exact ⟨original, output, kept, removed, hsys.symm ▸ ho, htsys.symm ▸ ht, hop, htp⟩


theorem replace_different_chains_profiled (S : RawPathSystem G Q)
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q) (hC : ∀ v ∈ C.getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q, ∃ original output kept removed : List ℕ,
      T.chains = P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length ∧
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  obtain ⟨T, hT, hTa⟩ := S.replace_different_chains hsys hA hC hJ hJQ hJpos hdis hpath
  obtain ⟨original, output, kept, removed, ho, ht, hp, hq⟩ :=
    S.replacement_profiles_different T hsys hT hA hC hJQ hJpos
  exact ⟨T, original, output, kept, removed, hT, hTa, ho, ht, hp, hq⟩

theorem replace_same_chain_profiled (S : RawPathSystem G Q)
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (hsys : S.chains = P ++ (A ++ (x :: B) ++ y :: D) :: R)
    (hA : ∀ v ∈ A.getLast?, v ∈ Q)
    (hB : ∀ v ∈ (x :: B).getLast?, v ∈ Q)
    (hJ : J.Nodup) (hJQ : ∀ z ∈ J, z ∉ Q) (hJpos : J ≠ [])
    (hdis : J.Disjoint S.chains.flatten)
    (hpath : (x :: (J ++ [y])).IsChain G.Adj) :
    ∃ T : RawPathSystem G Q, ∃ original output kept removed : List ℕ,
      T.chains = P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R ∧
      T.amount = S.amount + J.length ∧
      SystemAssignedAmounts Q S.chains original ∧
      SystemAssignedAmounts Q T.chains output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  obtain ⟨T, hT, hTa⟩ := S.replace_same_chain hsys hA hB hJ hJQ hJpos hdis hpath
  obtain ⟨original, output, kept, removed, ho, ht, hp, hq⟩ :=
    S.replacement_profiles_same T hsys hT hA hB hJQ hJpos
  exact ⟨T, original, output, kept, removed, hT, hTa, ho, ht, hp, hq⟩

end CycleClique.Construction.RawPathSystem

end OAI
