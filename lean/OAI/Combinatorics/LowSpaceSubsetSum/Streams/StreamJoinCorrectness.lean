import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamJoinBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.MatchFold

namespace OAI

/-! Exact callback semantics of the finite-state global join. -/

namespace LowSpaceSubsetSum
namespace StreamJoin

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def semanticAccount (key₁ : α → ℤ) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (view₁ : σ₁ → List α) (view₂ : σ₂ → List β)
    (st : State σ₁ σ₂ τ) : τ := MatchFold.run key₁ key₂ report (view₁ st.left) (view₂ st.right) st.user

theorem step_semantics (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (st : State σ₁ σ₂ τ)
    (hst : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ st) :
    semanticAccount key₁ key₂ report view₁ view₂
        (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st) =
      semanticAccount key₁ key₂ report view₁ view₂ st := by
  by_cases hd : st.done = true
  · rw [step_done _ _ _ _ _ _ _ _ st hd]
  have hdf := Bool.eq_false_iff.mpr hd
  cases hx : read₁ st.left with
  | none =>
    have hv : view₁ st.left = [] := by simpa only [hx] using hread₁ st.left
    simp only [step, hdf, Bool.false_eq_true, ite_false, hx, semanticAccount, hv, MatchFold.run]
  | some xp =>
    rcases xp with ⟨x, left'⟩
    have hv₁ : view₁ st.left = x :: view₁ left' := by simpa only [hx] using hread₁ st.left
    cases hy : read₂ st.right with
    | none =>
      have hv : view₂ st.right = [] := by simpa only [hy] using hread₂ st.right
      simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy, semanticAccount, hv,
        MatchFold.nil_right]
    | some yp =>
      rcases yp with ⟨y, right'⟩
      have hv₂ : view₂ st.right = y :: view₂ right' := by simpa only [hy] using hread₂ st.right
      by_cases hxy : key₁ x < key₂ y
      · have hlower₂ : ∀ z ∈ view₂ st.right, key₂ y ≤ key₂ z := by
          rw [hv₂]
          exact MatchPotential.lower_bound_head key₂ y _ (by simpa only [hv₂] using hst.2.1)
        simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy, ite_eq_left hxy, semanticAccount]
        rw [hv₁]
        exact (MatchFold.skip_left key₁ key₂ report x _ _ st.user
          (fun z hz => hxy.trans_le (hlower₂ z hz))).symm
      · by_cases hyx : key₂ y < key₁ x
        · have hlower₁ : ∀ z ∈ view₁ st.left, key₁ x ≤ key₁ z := by
            rw [hv₁]
            exact MatchPotential.lower_bound_head key₁ x _ (by simpa only [hv₁] using hst.1)
          simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy,
            ite_eq_right hxy, ite_eq_left hyx, semanticAccount]
          rw [hv₂]
          exact (MatchFold.skip_right key₁ key₂ report _ y _ st.user
            (fun z hz => hyx.trans_le (hlower₁ z hz))).symm
        · have hkey : key₁ x = key₂ y := by omega
          let out := TieGroup.run read₁ key₁ read₂ key₂ (key₁ x) report B fuel₁ fuel₂
            st.left st.right st.user
          let G₁ := TieBuffer.groupView key₁ (key₁ x) view₁ st.left
          let G₂ := TieBuffer.groupView key₂ (key₁ x) view₂ st.right
          have hg₁ : G₁ ≠ [] := by simp [G₁, TieBuffer.groupView, hv₁]
          have hcap₁ : G₁.length ≤ fuel₁ :=
            (List.takeWhile_sublist _).length_le.trans hst.2.2.1
          have hcap₂ : G₂.length ≤ fuel₂ :=
            (List.takeWhile_sublist _).length_le.trans hst.2.2.2
          have hviews := TieGroup.views_complete read₁ key₁ read₂ key₂ (key₁ x) report hreport
            view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st.left st.right st.user hcap₁ hcap₂ hg₁
          change view₁ st.left = G₁ ++ view₁ out.outer.cursor ∧
            view₂ st.right = G₂ ++ view₂ out.outer.state.last at hviews
          have hlower₁ : ∀ z ∈ view₁ st.left, key₁ x ≤ key₁ z := by
            rw [hv₁]
            exact MatchPotential.lower_bound_head key₁ x _ (by simpa only [hv₁] using hst.1)
          have hlower₂ : ∀ z ∈ view₂ st.right, key₁ x ≤ key₂ z := by
            rw [hkey, hv₂]
            exact MatchPotential.lower_bound_head key₂ y _ (by simpa only [hv₂] using hst.2.1)
          have hr₁ := MatchPotential.remaining_avoids key₁ (key₁ x) _ _ hviews.1 hst.1 hlower₁
          have hr₂ := MatchPotential.remaining_avoids key₂ (key₁ x) _ _ hviews.2 hst.2.1 hlower₂
          have hG₁ : ∀ z ∈ G₁, key₁ z = key₁ x := by
            intro z hz
            exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun z => decide (key₁ z = key₁ x)) hz)
          have hG₂ : ∀ z ∈ G₂, key₂ z = key₁ x := by
            intro z hz
            exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun z => decide (key₂ z = key₁ x)) hz)
          have hsplit := MatchFold.split_groups key₁ key₂ report (key₁ x) G₁
            (view₁ out.outer.cursor) G₂ (view₂ out.outer.state.last) st.user hG₁ hG₂ hr₁ hr₂
          rw [← hviews.1, ← hviews.2] at hsplit
          have hstate := TieGroup.state_complete read₁ key₁ read₂ key₂ (key₁ x) report hreport
            view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st.left st.right st.user hcap₁ hcap₂
          rw [← hstate] at hsplit
          simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy,
            ite_eq_right hxy, ite_eq_right hyx, semanticAccount]
          exact hsplit.symm

theorem runAcc_semantics (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (st : State σ₁ σ₂ τ)
    (hst : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ st) :
    semanticAccount key₁ key₂ report view₁ view₂
        (runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel st) =
      semanticAccount key₁ key₂ report view₁ view₂ st := by
  induction controlFuel generalizing st with
  | zero => rfl
  | succ controlFuel ih =>
    rw [runAcc, ih _ (step_accounts read₁ key₁ read₂ key₂ report hreport view₁ hread₁
      view₂ hread₂ B fuel₁ fuel₂ st hst).1]
    exact step_semantics read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st hst

def DoneEmpty (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (st : State σ₁ σ₂ τ) : Prop :=
  st.done = true → view₁ st.left = [] ∨ view₂ st.right = []

theorem step_doneEmpty (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (st : State σ₁ σ₂ τ) (hst : DoneEmpty view₁ view₂ st) :
    DoneEmpty view₁ view₂ (step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st) := by
  by_cases hd : st.done = true
  · rw [step_done _ _ _ _ _ _ _ _ st hd]
    exact hst
  have hdf := Bool.eq_false_iff.mpr hd
  cases hx : read₁ st.left with
  | none =>
    have hv : view₁ st.left = [] := by simpa only [hx] using hread₁ st.left
    simp only [DoneEmpty, step, hdf, Bool.false_eq_true, ite_false, hx]
    exact fun _ => Or.inl hv
  | some xp =>
    rcases xp with ⟨x, left'⟩
    cases hy : read₂ st.right with
    | none =>
      have hv : view₂ st.right = [] := by simpa only [hy] using hread₂ st.right
      simp only [DoneEmpty, step, hdf, Bool.false_eq_true, ite_false, hx, hy]
      exact fun _ => Or.inr hv
    | some yp =>
      rcases yp with ⟨y, right'⟩
      by_cases hxy : key₁ x < key₂ y
      · simp only [DoneEmpty, step, hdf, Bool.false_eq_true, ite_false, hx, hy, ite_eq_left hxy,
          false_implies]
      · by_cases hyx : key₂ y < key₁ x
        · simp only [DoneEmpty, step, hdf, Bool.false_eq_true, ite_false, hx, hy,
            ite_eq_right hxy, ite_eq_left hyx, false_implies]
        · have hhalt := TieGroup.halted_false read₁ key₁ read₂ key₂ (key₁ x) report hreport
            B fuel₁ fuel₂ st.left st.right st.user
          simp only [DoneEmpty, step, hdf, Bool.false_eq_true, ite_false, hx, hy,
            ite_eq_right hxy, ite_eq_right hyx, hhalt, false_implies]

theorem runAcc_doneEmpty (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (st : State σ₁ σ₂ τ) (hst : DoneEmpty view₁ view₂ st) :
    DoneEmpty view₁ view₂ (runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel st) := by
  induction controlFuel generalizing st with
  | zero => exact hst
  | succ controlFuel ih =>
    exact ih _ (step_doneEmpty read₁ key₁ read₂ key₂ report hreport
      view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st hst)

/-- Enough control fuel gives the exact Cartesian-match fold. Occurrences
with identical fields are still processed separately in this equation. -/
theorem run_complete (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂)
    (hfuel : (view₁ s₁).length + (view₂ s₂).length < controlFuel) :
    (run read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a).user =
      MatchFold.run key₁ key₂ report (view₁ s₁) (view₂ s₂) a := by
  have hw : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ (start s₁ s₂ a) :=
    ⟨hsort₁, hsort₂, hcap₁, hcap₂⟩
  have ht := runAcc_terminates read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ controlFuel (start s₁ s₂ a) hw hfuel
  have he := runAcc_doneEmpty read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ controlFuel (start s₁ s₂ a) (by simp [DoneEmpty, start])
  have hs := runAcc_semantics read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ controlFuel (start s₁ s₂ a) hw
  rcases he ht with hleft | hright
  · dsimp only [semanticAccount] at hs
    rw [hleft] at hs
    exact hs
  · dsimp only [semanticAccount] at hs
    rw [hright, MatchFold.nil_right] at hs
    exact hs

end StreamJoin
end LowSpaceSubsetSum

end OAI
