import OAI.Analysis.CircleDomains.Selection.PeriodBandGraph

namespace OAI

/-! Away from the finitely many marked singularities, every dust point
has a common neighborhood on which each masked coordinate is absent or
has one of its given real branches. The mask boundary lies in the domain. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 theorem exists_common_mask_branch_neighborhood
    {J : Type*} [Finite J] (I : J → Type*) (U : Set Sphere)
    (M : J → Set Sphere) (hM : ∀ j, IsClosed (M j))
    (hboundary : ∀ j, frontier (M j) ⊆ U)
    (b : J → Sphere) (V : ∀ j, I j → Set Sphere)
    (hV : ∀ j i, IsOpen (V j i))
    (hcover : ∀ j, M j \ {b j} ⊆ ⋃ i, V j i)
    {x : Sphere} (hx : x ∉ U) (hxb : ∀ j, x ≠ b j) :
    ∃ N : Set Sphere, IsOpen N ∧ x ∈ N ∧
      ∀ j, Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i := by
  classical
  have hlocal (j : J) : ∃ N : Set Sphere, IsOpen N ∧ x ∈ N ∧
      (Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i) := by
    by_cases hxm : x ∈ M j
    · have hxi : x ∈ interior (M j) :=
        (mem_interior_iff_notMem_frontier hxm).mpr (fun h => hx (hboundary j h))
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover j ⟨hxm, hxb j⟩)
      exact ⟨interior (M j) ∩ V j i, isOpen_interior.inter (hV j i),
        ⟨hxi, hi⟩, Or.inr ⟨i, Subset.rfl⟩⟩
    · exact ⟨(M j)ᶜ, (hM j).isOpen_compl, hxm, Or.inl disjoint_compl_left⟩
  choose N hNo hxN hchoice using hlocal
  refine ⟨⋂ j, N j, isOpen_iInter_of_finite hNo, mem_iInter.mpr hxN, ?_⟩
  intro j
  have hsub : (⋂ k, N k) ⊆ N j := iInter_subset N j
  rcases hchoice j with hd | ⟨i, hi⟩
  · exact Or.inl (hd.mono_left hsub)
  · exact Or.inr ⟨i, hsub.trans hi⟩


 theorem exists_common_mask_branch_neighborhood_of_subset
    {X J : Type*} [TopologicalSpace X] [Finite J] (I : J → Type*)
    (C : Set X) (M : J → Set X) (hM : ∀ j, IsClosed (M j))
    (V : ∀ j, I j → Set X) (hV : ∀ j i, IsOpen (V j i))
    (hchoice : ∀ j, Disjoint C (M j) ∨ ∃ i, C ⊆ interior (M j) ∩ V j i) :
    ∃ N : Set X, IsOpen N ∧ C ⊆ N ∧
      ∀ j, Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i := by
  have hlocal (j : J) : ∃ N : Set X, IsOpen N ∧ C ⊆ N ∧
      (Disjoint N (M j) ∨ ∃ i, N ⊆ interior (M j) ∩ V j i) := by
    rcases hchoice j with hd | ⟨i, hi⟩
    · exact ⟨(M j)ᶜ, (hM j).isOpen_compl, hd.subset_compl_right,
        Or.inl disjoint_compl_left⟩
    · exact ⟨interior (M j) ∩ V j i, isOpen_interior.inter (hV j i),
        hi, Or.inr ⟨i, Subset.rfl⟩⟩
  choose N hNo hCN hchoiceN using hlocal
  refine ⟨⋂ j, N j, isOpen_iInter_of_finite hNo,
    fun x hx => mem_iInter.mpr (fun j => hCN j hx), ?_⟩
  intro j
  have hsub : (⋂ k, N k) ⊆ N j := iInter_subset N j
  rcases hchoiceN j with hd | ⟨i, hi⟩
  · exact Or.inl (hd.mono_left hsub)
  · exact Or.inr ⟨i, hsub.trans hi⟩

end CircleDomainRigidity

end

end OAI
