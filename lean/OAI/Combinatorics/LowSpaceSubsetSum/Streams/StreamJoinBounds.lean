import OAI.Combinatorics.LowSpaceSubsetSum.Streams.StreamGroupFacts

namespace OAI

/-! Amortized accounts for the executable global stream join. -/

namespace LowSpaceSubsetSum
namespace StreamJoin

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def queryAccount (key₁ : α → ℤ) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (s : State σ₁ σ₂ τ) : ℕ :=
  s.queries + 6 * rank view₁ view₂ s + potential key₁ key₂ view₁ view₂ s + if s.done then 0 else 2

def reportAccount (key₁ : α → ℤ) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (s : State σ₁ σ₂ τ) : ℕ :=
  s.reports + potential key₁ key₂ view₁ view₂ s

def copyAccount (key₁ : α → ℤ) (key₂ : β → ℤ)
    (view₁ : σ₁ → List α) (view₂ : σ₂ → List β) (B : ℕ) (s : State σ₁ σ₂ τ) : ℕ :=
  B * s.copies + 2 * potential key₁ key₂ view₁ view₂ s

theorem step_accounts (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ : ℕ) (st : State σ₁ σ₂ τ)
    (hst : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ st) :
    let next := step read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ st
    WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ next ∧
    queryAccount key₁ key₂ view₁ view₂ next ≤ queryAccount key₁ key₂ view₁ view₂ st ∧
    reportAccount key₁ key₂ view₁ view₂ next ≤ reportAccount key₁ key₂ view₁ view₂ st ∧
    copyAccount key₁ key₂ view₁ view₂ B next ≤ copyAccount key₁ key₂ view₁ view₂ B st ∧
    (st.done = false → next.done = true ∨ rank view₁ view₂ next < rank view₁ view₂ st) := by
  by_cases hd : st.done = true
  · simp only [step_done _ _ _ _ _ _ _ _ st hd, le_refl, hd, Bool.true_eq_false,
      false_implies, and_true]
    exact hst
  have hdf : st.done = false := Bool.eq_false_iff.mpr hd
  cases hx : read₁ st.left with
  | none =>
    simp only [step, hdf, Bool.false_eq_true, ite_false, hx]
    refine ⟨hst, ?_, le_rfl, le_rfl, ?_⟩
    · dsimp only [queryAccount, rank, potential]
      simp only [hdf, Bool.false_eq_true, ↓reduceIte]
      omega
    · simp
  | some xp =>
    rcases xp with ⟨x, left'⟩
    have hv₁ : view₁ st.left = x :: view₁ left' := by simpa only [hx] using hread₁ st.left
    cases hy : read₂ st.right with
    | none =>
      simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy]
      refine ⟨hst, ?_, le_rfl, le_rfl, ?_⟩
      · dsimp only [queryAccount, rank, potential]
        simp only [hdf, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp
    | some yp =>
      rcases yp with ⟨y, right'⟩
      have hv₂ : view₂ st.right = y :: view₂ right' := by simpa only [hy] using hread₂ st.right
      by_cases hxy : key₁ x < key₂ y
      · have hsort₁ := hst.1
        rw [hv₁] at hsort₁
        have hlower₂ := MatchPotential.lower_bound_head key₂ y (view₂ right')
          (show (y :: view₂ right').Pairwise (fun x y => key₂ x ≤ key₂ y) from
            by simpa only [hv₂] using hst.2.1)
        have hp : MatchPotential.count key₁ key₂ (view₁ st.left) (view₂ st.right) =
            MatchPotential.count key₁ key₂ (view₁ left') (view₂ st.right) := by
          rw [hv₁]
          apply MatchPotential.skip_left
          intro z hz
          exact hxy.trans_le (hlower₂ z (by simpa only [hv₂] using hz))
        simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy, ite_eq_left hxy]
        refine ⟨⟨(List.pairwise_cons.mp hsort₁).2, hst.2.1, ?_, hst.2.2.2⟩, ?_, ?_, ?_, ?_⟩
        · have hc := hst.2.2.1
          rw [hv₁, List.length_cons] at hc
          dsimp only
          omega
        · dsimp only [queryAccount, rank, potential]
          simp only [hdf, Bool.false_eq_true, ite_false]
          rw [← hp, hv₁, List.length_cons]
          omega
        · dsimp only [reportAccount, potential]
          rw [hp]
        · dsimp only [copyAccount, potential]
          rw [hp]
        · intro _
          right
          dsimp only [rank]
          rw [hv₁, List.length_cons]
          omega
      · by_cases hyx : key₂ y < key₁ x
        · have hsort₂ := hst.2.1
          rw [hv₂] at hsort₂
          have hlower₁ := MatchPotential.lower_bound_head key₁ x (view₁ left')
            (show (x :: view₁ left').Pairwise (fun x y => key₁ x ≤ key₁ y) from
              by simpa only [hv₁] using hst.1)
          have hp : MatchPotential.count key₁ key₂ (view₁ st.left) (view₂ st.right) =
              MatchPotential.count key₁ key₂ (view₁ st.left) (view₂ right') := by
            rw [hv₂]
            apply MatchPotential.skip_right
            intro z hz
            exact hyx.trans_le (hlower₁ z (by simpa only [hv₁] using hz))
          simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy,
            ite_eq_right hxy, ite_eq_left hyx]
          refine ⟨⟨hst.1, (List.pairwise_cons.mp hsort₂).2, hst.2.2.1, ?_⟩, ?_, ?_, ?_, ?_⟩
          · have hc := hst.2.2.2
            rw [hv₂, List.length_cons] at hc
            dsimp only
            omega
          · dsimp only [queryAccount, rank, potential]
            simp only [hdf, Bool.false_eq_true, ite_false]
            rw [← hp, hv₂, List.length_cons]
            omega
          · dsimp only [reportAccount, potential]
            rw [hp]
          · dsimp only [copyAccount, potential]
            rw [hp]
          · intro _
            right
            dsimp only [rank]
            rw [hv₂, List.length_cons]
            omega
        · have hkey : key₁ x = key₂ y := by omega
          let out := TieGroup.run read₁ key₁ read₂ key₂ (key₁ x) report B fuel₁ fuel₂
            st.left st.right st.user
          have hg := equal_group_facts read₁ key₁ read₂ key₂ report hreport
            view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st hst x left' y right' hx hy hkey
          rcases hg with ⟨hs₁, hs₂, hl₁, hl₂, hn₁, hn₂, hp⟩
          have hq := TieGroup.query_bound read₁ key₁ read₂ key₂ (key₁ x) report
            view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st.left st.right st.user
          have hr := (TieGroup.run_bounds read₁ key₁ read₂ key₂ (key₁ x) report
            view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st.left st.right st.user).1
          have hc := TieGroup.copies_charged read₁ key₁ read₂ key₂ (key₁ x) report
            view₁ hread₁ view₂ hread₂ B fuel₁ fuel₂ st.left st.right st.user
          have hhalt : out.outer.halted = false := TieGroup.halted_false
            read₁ key₁ read₂ key₂ (key₁ x) report hreport B fuel₁ fuel₂ st.left st.right st.user
          dsimp only [out] at hhalt
          simp only [step, hdf, Bool.false_eq_true, ite_false, hx, hy,
            ite_eq_right hxy, ite_eq_right hyx]
          change WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂
            (⟨out.outer.cursor, out.outer.state.last, out.outer.state.user,
              st.queries + 2 + out.outer.queries + out.fillQueries + out.outer.state.queries,
              st.reports + out.outer.state.reports,
              st.copies + (if out.snapshot then 1 else 0) + out.outer.state.restores,
              out.outer.halted⟩ : State σ₁ σ₂ τ) ∧ _
          refine ⟨⟨hs₁, hs₂, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · have hcap := hst.2.2.1
            dsimp only [out]
            omega
          · have hcap := hst.2.2.2
            dsimp only [out]
            omega
          · dsimp only [queryAccount, rank, potential]
            simp only [hhalt, hdf, Bool.false_eq_true, ite_false]
            nlinarith
          · dsimp only [reportAccount, potential]
            omega
          · dsimp only [copyAccount, potential]
            nlinarith
          · intro _
            right
            dsimp only [rank]
            omega

theorem runAcc_accounts (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (st : State σ₁ σ₂ τ)
    (hst : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ st) :
    let out := runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel st
    WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ out ∧
    queryAccount key₁ key₂ view₁ view₂ out ≤ queryAccount key₁ key₂ view₁ view₂ st ∧
    reportAccount key₁ key₂ view₁ view₂ out ≤ reportAccount key₁ key₂ view₁ view₂ st ∧
    copyAccount key₁ key₂ view₁ view₂ B out ≤ copyAccount key₁ key₂ view₁ view₂ B st := by
  induction controlFuel generalizing st with
  | zero => exact ⟨hst, le_rfl, le_rfl, le_rfl⟩
  | succ controlFuel ih =>
    have hs := step_accounts read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂
      B fuel₁ fuel₂ st hst
    have hi := ih _ hs.1
    exact ⟨hi.1, hi.2.1.trans hs.2.1, hi.2.2.1.trans hs.2.2.1,
      hi.2.2.2.trans hs.2.2.2.1⟩

theorem runAcc_terminates (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (st : State σ₁ σ₂ τ)
    (hst : WellFormed key₁ key₂ view₁ view₂ fuel₁ fuel₂ st)
    (hfuel : rank view₁ view₂ st < controlFuel) :
    (runAcc read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel st).done = true := by
  induction controlFuel generalizing st with
  | zero => omega
  | succ controlFuel ih =>
    by_cases hd : st.done = true
    · rw [runAcc_done _ _ _ _ _ _ _ _ _ st hd]
      exact hd
    have hs := step_accounts read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂
      B fuel₁ fuel₂ st hst
    rcases hs.2.2.2.2 (Bool.eq_false_iff.mpr hd) with hdone | hprogress
    · rw [runAcc, runAcc_done _ _ _ _ _ _ _ _ _ _ hdone]
      exact hdone
    · rw [runAcc]
      exact ih _ hs.1 (by omega)

theorem run_bounds (read₁ : σ₁ → Option (α × σ₁)) (key₁ : α → ℤ)
    (read₂ : σ₂ → Option (β × σ₂)) (key₂ : β → ℤ)
    (report : α → β → τ → τ × Bool) (hreport : ∀ x y a, (report x y a).2 = false)
    (view₁ : σ₁ → List α) (hread₁ : RowMerge.IsReader read₁ view₁)
    (view₂ : σ₂ → List β) (hread₂ : RowMerge.IsReader read₂ view₂)
    (B fuel₁ fuel₂ controlFuel : ℕ) (s₁ : σ₁) (s₂ : σ₂) (a : τ)
    (hsort₁ : (view₁ s₁).Pairwise (fun x y => key₁ x ≤ key₁ y))
    (hsort₂ : (view₂ s₂).Pairwise (fun x y => key₂ x ≤ key₂ y))
    (hcap₁ : (view₁ s₁).length ≤ fuel₁) (hcap₂ : (view₂ s₂).length ≤ fuel₂) :
    let out := run read₁ key₁ read₂ key₂ report B fuel₁ fuel₂ controlFuel s₁ s₂ a
    out.queries ≤ 6 * ((view₁ s₁).length + (view₂ s₂).length) +
        MatchPotential.count key₁ key₂ (view₁ s₁) (view₂ s₂) + 2 ∧
    out.reports ≤ MatchPotential.count key₁ key₂ (view₁ s₁) (view₂ s₂) ∧
    B * out.copies ≤ 2 * MatchPotential.count key₁ key₂ (view₁ s₁) (view₂ s₂) := by
  have h := runAcc_accounts read₁ key₁ read₂ key₂ report hreport view₁ hread₁ view₂ hread₂
    B fuel₁ fuel₂ controlFuel (start s₁ s₂ a) ⟨hsort₁, hsort₂, hcap₁, hcap₂⟩
  have hq := h.2.1
  have hr := h.2.2.1
  have hc := h.2.2.2
  dsimp only [queryAccount, reportAccount, copyAccount, rank, potential, start] at hq hr hc
  simp only [Bool.false_eq_true, ite_false, Nat.zero_add, Nat.mul_zero] at hq hr hc
  dsimp only [run, start]
  omega

end StreamJoin
end LowSpaceSubsetSum

end OAI
