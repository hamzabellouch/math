import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorAverage

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem movingFieldGiantAmplitude_norm_le {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (D : (ZMod q)ˣ) {n C : ℕ} (T : MovingGiantTree n C)
    (x y : ZMod q) (z : TreeLeafTuple (ZMod q)ˣ n) :
    ‖movingFieldGiantAmplitude g D T x y z‖ ≤ K ^ (2 ^ n) := by
  induction T generalizing x y with
  | leaf s C =>
    simpa only [movingFieldGiantAmplitude, pow_zero, pow_one] using hg _
  | @node n s CL CR u left right ihL ihR =>
    simp only [movingFieldGiantAmplitude]
    split_ifs
    · simpa only [norm_zero] using pow_nonneg hK (2 ^ (n + 1))
    · rw [norm_mul, Complex.norm_conj]
      calc
        _ ≤ K ^ (2 ^ n) * K ^ (2 ^ n) :=
          mul_le_mul (ihL _ _ _) (ihR _ _ _) (norm_nonneg _) (pow_nonneg hK _)
        _ = K ^ (2 ^ (n + 1)) := by
          rw [← pow_add, pow_succ]
          congr 1
          omega

theorem frozenBulkSpectatorPair_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (a : (ZMod q)ˣ × (ZMod q)ˣ) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorPair base n m t small samples D e g a z‖ ≤ K ^ (2 ^ (n + 1)) := by
  rw [frozenBulkSpectatorPair, norm_mul, Complex.norm_conj]
  calc
    _ ≤ K ^ (2 ^ n) * K ^ (2 ^ n) :=
      mul_le_mul (movingFieldGiantAmplitude_norm_le g K hK hg _ _ _ _ _)
        (movingFieldGiantAmplitude_norm_le g K hK hg _ _ _ _ _) (norm_nonneg _) (pow_nonneg hK _)
    _ = K ^ (2 ^ (n + 1)) := by rw [← pow_add, pow_succ]; congr 1; omega

/-- The mixed Haar normalization has norm at most one, so the field bound
survives without a factor depending on the spectator prime. -/
theorem frozenBulkSpectatorHaar_norm_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ x, ‖g x‖ ≤ K)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
    ‖frozenBulkSpectatorHaar base n m t small samples D e g z‖ ≤ K ^ (2 ^ (n + 1)) := by
  let A := (ZMod q)ˣ × (ZMod q)ˣ
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : ‖(Fintype.card A : ℂ)⁻¹ * ∑ a : A,
      frozenBulkSpectatorPair base n m t small samples D e g a z‖ ≤ K ^ (2 ^ (n + 1)) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (Fintype.card A : ℝ)⁻¹ * ∑ _a : A, K ^ (2 ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
          frozenBulkSpectatorPair_norm_le base n m t small samples D e g K hK hg a z))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K ^ (2 ^ (n + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hr : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by exact_mod_cast (Fact.out : q.Prime).pos)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  rw [frozenBulkSpectatorHaar, norm_mul]
  exact (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (pow_nonneg hK (2 ^ (n + 1))))

end Ostmann

end OAI
