import OAI.NumberTheory.JointDickman.Counting.EntropyWindowStability

namespace OAI

/-! # Counting omission subsets in a regularity window -/

namespace JointDickman
open Finset Classical

noncomputable def subsetCardWindow (P : Finset ℕ) (ℓ g r τ : ℝ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun A => |(A.card : ℝ)/ℓ-g*r| ≤ 3*τ)

theorem subset_card_window_entropy {g ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (P : Finset ℕ) (ℓ r τ : ℝ),
      0 < ℓ → 0 ≤ τ → τ ≤ τ₀ → 0 ≤ r → r ≤ 1/2 →
      |(P.card : ℝ)/ℓ-g/2| ≤ τ →
      ((subsetCardWindow P ℓ g r τ).card : ℝ) ≤
        ((P.card : ℝ)+1)*Real.exp (((g/2)*Real.binEntropy (2*r)+ε)*ℓ) := by
  obtain ⟨τ₁,hτ₁,hstab⟩ := entropy_window_stability hg hε
  let τ₀ := min τ₁ (g/4)
  refine ⟨τ₀,lt_min hτ₁ (by positivity),?_⟩
  intro P ℓ r τ hℓ hτ hτsmall hr hr1 hP
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτg : τ ≤ g/4 := hτsmall.trans (min_le_right _ _)
  have hPpos : (0 : ℝ) < P.card := by
    have ha := (abs_le.mp hP).1
    have hx : 0 < (P.card : ℝ)/ℓ := by linarith
    exact ((div_pos_iff.mp hx).resolve_right (by intro h; linarith)).1
  have hbound (k : ℕ) (hk : k ≤ P.card) (hwin : |(k : ℝ)/ℓ-g*r| ≤ 3*τ) :
      ((P.powerset.filter (fun A => A.card = k)).card : ℝ) ≤
        Real.exp (((g/2)*Real.binEntropy (2*r)+ε)*ℓ) := by
    have he := hstab τ ((P.card : ℝ)/ℓ) ((k : ℝ)/ℓ) r hτ hτ₁' hr hr1 hP hwin
    have hd : ((k : ℝ)/ℓ)/((P.card : ℝ)/ℓ) = (k : ℝ)/P.card := by
      field_simp
    rw [hd] at he
    have hm := mul_le_mul_of_nonneg_right he hℓ.le
    have hn : (P.card : ℝ)/ℓ*Real.binEntropy ((k : ℝ)/P.card)*ℓ =
        (P.card : ℝ)*Real.binEntropy ((k : ℝ)/P.card) := by field_simp
    rw [hn] at hm
    exact (subset_exact_count_entropy P hk).trans (Real.exp_le_exp.mpr hm)
  let F := subsetCardWindow P ℓ g r τ
  have hcard : F.card = ∑ k ∈ range (P.card+1), (F.filter (fun A => A.card = k)).card := by
    apply card_eq_sum_card_fiberwise
    intro A hA
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp (mem_filter.mp hA).1)))
  rw [hcard,Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ range (P.card+1), Real.exp (((g/2)*Real.binEntropy (2*r)+ε)*ℓ) := by
      apply sum_le_sum
      intro k hk
      by_cases hwin : |(k : ℝ)/ℓ-g*r| ≤ 3*τ
      · have hsub : F.filter (fun A => A.card = k) ⊆ P.powerset.filter (fun A => A.card = k) := by
          intro A hA
          exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hA).1).1,(mem_filter.mp hA).2⟩
        exact (show ((F.filter (fun A => A.card = k)).card : ℝ) ≤
          (P.powerset.filter (fun A => A.card = k)).card by exact_mod_cast card_le_card hsub).trans
            (hbound k (Nat.le_of_lt_succ (mem_range.mp hk)) hwin)
      · have hf : F.filter (fun A => A.card = k) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro A hA
          have ha := mem_filter.mp hA
          have hw := (mem_filter.mp ha.1).2
          rw [ha.2] at hw
          exact hwin hw
        rw [hf,card_empty,Nat.cast_zero]
        exact (Real.exp_pos _).le
    _ = _ := by simp [Nat.cast_add,Nat.cast_one]

end JointDickman

end OAI
