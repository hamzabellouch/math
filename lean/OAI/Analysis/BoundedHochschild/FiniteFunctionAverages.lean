import OAI.Analysis.BoundedHochschild.FiniteGroupCochainAverages

namespace OAI

/-! Deleting one independently averaged finite coordinate leaves the
normalized average unchanged. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {G V : Type*} [Fintype G] [Nonempty G] [AddCommGroup V] [Module ℂ V]

omit [Nonempty G] in
lemma sum_removeNth {n : ℕ} (k : Fin (n + 1)) (F : (Fin n → G) → V) :
    (∑ u : Fin (n + 1) → G, F (k.removeNth u)) =
      (Fintype.card G : ℂ) • ∑ v : Fin n → G, F v := by
  calc
    _ = ∑ p : G × (Fin n → G), F p.2 := by
      apply Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => G) k).symm _ _
      intro u
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

lemma normalized_sum_removeNth {n : ℕ} (k : Fin (n + 1)) (F : (Fin n → G) → V) :
    (Fintype.card (Fin (n + 1) → G) : ℂ)⁻¹ • (∑ u : Fin (n + 1) → G, F (k.removeNth u)) =
      (Fintype.card (Fin n → G) : ℂ)⁻¹ • ∑ v : Fin n → G, F v := by
  rw [sum_removeNth, smul_smul]
  congr 1
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, pow_succ, Nat.cast_mul]
  field_simp

end BoundedHochschild.KadisonRingrose

end

end OAI
