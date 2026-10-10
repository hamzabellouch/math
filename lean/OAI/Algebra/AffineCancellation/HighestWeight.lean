import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.SL2
variable {R : Type*} [AddCommGroup R] [Module ℂ R]

/-- A highest weight vector in a locally finite sl₂ representation has nonnegative
weight. Only local nilpotence of the lowering operator on this vector is needed. -/
lemma no_negative_highest (δ η H : R →ₗ[ℂ] R)
    (hcomm : ∀ r, δ (η r) - η (δ r) = H r)
    (hlower : ∀ r, H (η r) = η (H r) - (2 : ℂ) • η r)
    (r : R) (w : ℤ) (hw : w < 0) (hδ : δ r = 0)
    (hH : H r = (w : ℂ) • r) (hη : ∃ n : ℕ, (η : R → R)^[n] r = 0) : r = 0 := by
  have hweight : ∀ n : ℕ, H ((η : R → R)^[n] r) =
      ((w : ℂ) - 2 * n) • ((η : R → R)^[n] r) := by
    intro n
    induction n with
    | zero => simpa using hH
    | succ n ih =>
      rw [Function.iterate_succ_apply', hlower, ih, map_smul]
      rw [← sub_smul]
      congr 1
      push_cast
      ring
  have hraise : ∀ n : ℕ, δ ((η : R → R)^[n+1] r) =
      (((n+1 : ℕ) : ℂ) * ((w : ℂ) - n)) • ((η : R → R)^[n] r) := by
    intro n
    induction n with
    | zero =>
      have hh := hcomm r
      simpa [hδ, hH] using (sub_eq_iff_eq_add.mp hh)
    | succ n ih =>
      rw [Function.iterate_succ_apply', sub_eq_iff_eq_add.mp (hcomm _)]
      rw [hweight, ih, map_smul]
      rw [← Function.iterate_succ_apply' η n r, ← add_smul]
      congr 1
      push_cast
      ring
  by_contra hr
  obtain ⟨n, hn⟩ := hη
  have nz : ∀ n : ℕ, (η : R → R)^[n] r ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hr
    | succ n ih =>
      intro hh
      have he := hraise n
      rw [hh, map_zero] at he
      have hc : ((↑(n+1) : ℂ) * ((w : ℂ) - n)) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast Nat.succ_ne_zero n
        · intro hh
          have hw' : (w : ℂ) = (n : ℂ) := sub_eq_zero.mp hh
          have heq : w = (n : ℤ) := by exact_mod_cast hw'
          omega
      exact ih ((smul_eq_zero.mp he.symm).resolve_left hc)
  exact nz n hn

end ComplexCancellation.SL2

end

end OAI
