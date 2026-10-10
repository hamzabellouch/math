import OAI.NumberTheory.Ostmann.Construction.ScheduledInputPhase

namespace OAI

/-! # Exact constituent-prime support at the pivot/H/Y partition -/

namespace Ostmann

open scoped BigOperators Classical

theorem pivot_retained_pairwise_iff {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (x : Fin r → P)
    (L : H → ℕ) (U : Y → ℕ) :
    Pairwise (fun i j =>
      (Sum.elim (fun k => (x k : ℕ)) (Sum.elim L U) i).Coprime
        (Sum.elim (fun k => (x k : ℕ)) (Sum.elim L U) j)) ↔
      Function.Injective x ∧
      Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)) ∧
      (∏ k, (x k : ℕ)).Coprime ((∏ h, L h) * ∏ y, U y) := by
  constructor
  · intro h
    have hi : Function.Injective x := by
      intro i j he
      by_contra hij
      have hc := h (show Sum.inl i ≠ Sum.inl j from fun he => hij (Sum.inl.inj he))
      change (x i : ℕ).Coprime (x j : ℕ) at hc
      rw [he] at hc
      have hone : (x j : ℕ) = 1 := by simpa only [Nat.coprime_self] using hc
      exact (hP _ (x j).property).ne_one hone
    have hb : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)) := by
      intro i j hij
      exact h (show Sum.inr i ≠ Sum.inr j from fun he => hij (Sum.inr.inj he))
    have hm : (∏ k, (x k : ℕ)).Coprime (∏ j : H ⊕ Y, Sum.elim L U j) := by
      apply Nat.coprime_fintype_prod_left_iff.mpr
      intro i
      apply Nat.coprime_fintype_prod_right_iff.mpr
      intro j
      exact h (show Sum.inl i ≠ Sum.inr j from by
        intro he
        cases he)
    exact ⟨hi, hb, by simpa only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] using hm⟩
  · rintro ⟨hi, hb, hm⟩
    apply pivot_retained_pairwise (fun k => (x k : ℕ)) L U _ hb hm
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hi (Subtype.ext he))

end Ostmann

end OAI
