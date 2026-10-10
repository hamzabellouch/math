import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamJoin

namespace OAI

/-! The exact potential and cursor facts for one equal-key stream step. -/

namespace LowSpaceSubsetSum
namespace StreamJoin

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

theorem equal_group_facts (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (st : State σ₁ σ₂ τ)
    (hst : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ st)
    (x : α) (left' : σ₁) (y : β) (right' : σ₂)
    (hx : read₁ st.left = some (x, left')) (hy : read₂ st.right = some (y, right'))
    (hkey : key₁ x = key₂ y) :
    let out := TieGroup.run read₁ key₁ read₂ key₂ (key₁ x) report B fuel₁ fuel₂
      st.left st.right st.user
    let G₁ := TieBuffer.groupView key₁ (key₁ x) view₁ st.left
    let G₂ := TieBuffer.groupView key₂ (key₁ x) view₂ st.right
    (view₁ out.outer.cursor).Pairwise (fun x y => key₁ x ≤ key₁ y) ∧
    (view₂ out.outer.state.last).Pairwise (fun x y => key₂ x ≤ key₂ y) ∧
    (view₁ st.left).length = G₁.length + (view₁ out.outer.cursor).length ∧
    (view₂ st.right).length = G₂.length + (view₂ out.outer.state.last).length ∧
    0 < G₁.length ∧ 0 < G₂.length ∧
    MatchPotential.count key₁ key₂ (view₁ st.left) (view₂ st.right) =
      G₁.length * G₂.length +
        MatchPotential.count key₁ key₂ (view₁ out.outer.cursor) (view₂ out.outer.state.last) := by
  let out := TieGroup.run read₁ key₁ read₂ key₂ (key₁ x) report B fuel₁ fuel₂
    st.left st.right st.user
  let G₁ := TieBuffer.groupView key₁ (key₁ x) view₁ st.left
  let G₂ := TieBuffer.groupView key₂ (key₁ x) view₂ st.right
  have hv₁ : view₁ st.left = x :: view₁ left' := by simpa only [hx] using hread₁ st.left
  have hv₂ : view₂ st.right = y :: view₂ right' := by simpa only [hy] using hread₂ st.right
  have hg₁ : G₁ ≠ [] := by simp [G₁, TieBuffer.groupView, hv₁]
  have hg₂ : G₂ ≠ [] := by simp [G₂, TieBuffer.groupView, hv₂, ← hkey]
  have hlen₁ : G₁.length ≤ fuel₁ :=
    (List.takeWhile_sublist (fun z => decide (key₁ z = key₁ x))).length_le.trans hst.2.2.1
  have hlen₂ : G₂.length ≤ fuel₂ :=
    (List.takeWhile_sublist (fun z => decide (key₂ z = key₁ x))).length_le.trans hst.2.2.2
  have hviews := TieGroup.views_complete read₁ key₁ read₂ key₂ (key₁ x) report hreport
    view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st.left st.right st.user hlen₁ hlen₂ hg₁
  change view₁ st.left = G₁ ++ view₁ out.outer.cursor ∧
    view₂ st.right = G₂ ++ view₂ out.outer.state.last at hviews
  have hsub₁ := MatchPotential.remaining_sublist _ _ _ hviews.1
  have hsub₂ := MatchPotential.remaining_sublist _ _ _ hviews.2
  have hlower₁ : ∀ z ∈ view₁ st.left, key₁ x ≤ key₁ z := by
    have hsort : (x :: view₁ left').Pairwise (fun x y => key₁ x ≤ key₁ y) :=
      by simpa only [hv₁] using hst.1
    simpa only [hv₁] using MatchPotential.lower_bound_head key₁ x _ hsort
  have hlower₂ : ∀ z ∈ view₂ st.right, key₁ x ≤ key₂ z := by
    rw [hkey, hv₂]
    exact MatchPotential.lower_bound_head key₂ y _ (by simpa only [hv₂] using hst.2.1)
  have hr₁ := MatchPotential.remaining_avoids key₁ (key₁ x) _ _ hviews.1 hst.1 hlower₁
  have hr₂ := MatchPotential.remaining_avoids key₂ (key₁ x) _ _ hviews.2 hst.2.1 hlower₂
  refine ⟨hst.1.sublist hsub₁, hst.2.1.sublist hsub₂, ?_, ?_,
    List.length_pos_iff.mpr hg₁, List.length_pos_iff.mpr hg₂, ?_⟩
  · simpa only [List.length_append] using congrArg List.length hviews.1
  · simpa only [List.length_append] using congrArg List.length hviews.2
  · have hG₁ : ∀ z ∈ G₁, key₁ z = key₁ x := by
      intro z hz
      exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun z => decide (key₁ z = key₁ x)) hz)
    have hG₂ : ∀ z ∈ G₂, key₂ z = key₁ x := by
      intro z hz
      exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun z => decide (key₂ z = key₁ x)) hz)
    have hsplit := MatchPotential.split_groups key₁ key₂ (key₁ x) G₁
      (view₁ out.outer.cursor) G₂ (view₂ out.outer.state.last) hG₁ hG₂ hr₁ hr₂
    rw [← hviews.1, ← hviews.2] at hsplit
    exact hsplit

end StreamJoin
end LowSpaceSubsetSum

end OAI
