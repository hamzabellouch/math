import OAI.NumberTheory.Ostmann.Arithmetic.ReversalCoprimality

namespace OAI

namespace Ostmann.Arithmetic.HistorySupportDescent

theorem products_coprime {A B O : List ℕ}
    (h : (A ++ (B ++ O)).Pairwise Nat.Coprime) : Nat.Coprime A.prod B.prod := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro a ha
  apply Nat.coprime_list_prod_right_iff.mpr
  intro b hb
  exact (List.pairwise_append.mp h).2.2 a ha b (List.mem_append_left O hb)

theorem pivot_coprime_compensation {u : List ℕ} {p : ℕ} {s N : ℤ}
    (hu : ∀ b ∈ u, Nat.Prime b)
    (hN : N = s * (u.prod : ℤ) * (p : ℤ))
    (hsq : ∀ b ∈ u, ¬ (b : ℤ) * b ∣ N) :
    ∀ b ∈ u, Nat.Coprime p b := by
  intro b hb
  apply Nat.Coprime.symm
  apply (hu b hb).coprime_iff_not_dvd.mpr
  intro hbp
  have hbu : (b : ℤ) ∣ (u.prod : ℤ) := by exact_mod_cast List.dvd_prod hb
  have hbp' : (b : ℤ) ∣ (p : ℤ) := by exact_mod_cast hbp
  apply hsq b hb
  rw [hN, mul_assoc]
  exact dvd_mul_of_dvd_right (mul_dvd_mul hbu hbp') s

theorem children_pairwise {A B u O : List ℕ} {p : ℕ} {v w s : ℤ}
    (hparent : (A ++ (B ++ O)).Pairwise Nat.Coprime)
    (hv : IsCoprime v (A.prod : ℤ)) (hw : IsCoprime w (B.prod : ℤ))
    (hN : reversalNumerator v w (A.prod : ℤ) (B.prod : ℤ) =
      s * (u.prod : ℤ) * (p : ℤ))
    (hu : u.Pairwise Nat.Coprime) (huprime : ∀ b ∈ u, Nat.Prime b)
    (hsq : ∀ b ∈ u, ¬ (b : ℤ) * b ∣ reversalNumerator v w (A.prod : ℤ) (B.prod : ℤ))
    (hpO : ∀ a ∈ O, Nat.Coprime p a)
    (huO : ∀ b ∈ u, ∀ a ∈ O, Nat.Coprime b a) :
    (p :: (u ++ (A ++ O))).Pairwise Nat.Coprime ∧
      (p :: (u ++ (B ++ O))).Pairwise Nat.Coprime := by
  have hH : IsCoprime (A.prod : ℤ) (B.prod : ℤ) := (products_coprime hparent).isCoprime
  have hinherited : ∀ a, a ∈ A ∨ a ∈ B → Nat.Coprime p a ∧ Nat.Coprime u.prod a := by
    intro a ha
    have hd : (a : ℤ) ∣ (A.prod : ℤ) ∨ (a : ℤ) ∣ (B.prod : ℤ) := by
      rcases ha with ha | ha
      · left; exact_mod_cast List.dvd_prod ha
      · right; exact_mod_cast List.dvd_prod ha
    obtain ⟨hp,hu⟩ := integral_reversal_inherited_coprime hH hv hw hN hd
    exact ⟨hp.natCoprime,hu.natCoprime⟩
  have hpu := pivot_coprime_compensation huprime hN hsq
  have hsplit := List.pairwise_append.mp hparent
  have hsplit' := List.pairwise_append.mp hsplit.2.1
  have hAO : (A ++ O).Pairwise Nat.Coprime := List.pairwise_append.mpr
    ⟨hsplit.1,hsplit'.2.1,fun a ha b hb => hsplit.2.2 a ha b (List.mem_append_right B hb)⟩
  have hBO : (B ++ O).Pairwise Nat.Coprime := hsplit.2.1
  have hchild : ∀ T : List ℕ, (∀ a ∈ T, a ∈ A ∨ a ∈ B) →
      (T ++ O).Pairwise Nat.Coprime → (p :: (u ++ (T ++ O))).Pairwise Nat.Coprime := by
    intro T hT hTO
    apply List.pairwise_cons.mpr
    constructor
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hpu a ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact (hinherited a (hT a ha)).1
        · exact hpO a ha
    · apply List.pairwise_append.mpr
      refine ⟨hu,hTO,?_⟩
      intro b hb a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact Nat.coprime_list_prod_left_iff.mp (hinherited a (hT a ha)).2 b hb
      · exact huO b hb a ha
  exact ⟨hchild A (fun a ha => Or.inl ha) hAO, hchild B (fun a ha => Or.inr ha) hBO⟩

end Ostmann.Arithmetic.HistorySupportDescent

end OAI
