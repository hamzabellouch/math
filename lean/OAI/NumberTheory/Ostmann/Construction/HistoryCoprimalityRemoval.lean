import OAI.NumberTheory.Ostmann.ZeroDensity.ZeroVariableHistory

namespace OAI

/-! # Removing the actual large-prime coprimalities of reconstructed histories -/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_dvd_cleared_iff (p : ℕ) (hp : p.Prime) (N d y : ℤ)
    (hN : N = d * y) (hd : ¬p ∣ d.natAbs) :
    p ∣ N.natAbs ↔ p ∣ y.natAbs := by
  simp only [hN, Int.natAbs_mul, hp.dvd_mul, hd, false_or]

/-- The zero-polynomial branch has empty valid support, including when the
reconstructed integer is represented by a cleared numerator. -/
theorem zero_cleared_history_support {σ : Type*} (P : MvPolynomial σ ℤ)
    (i : σ) (hP : zeroHistoryVariable i P = 0) (x : σ → ℤ)
    (p : ℕ) (hp : p.Prime) (hxi : x i = p) (d y : ℤ)
    (hN : MvPolynomial.eval₂Hom (RingHom.id ℤ) x P = d * y)
    (hd : ¬p ∣ d.natAbs) : ¬p.Coprime y.natAbs := by
  rw [hp.coprime_iff_not_dvd, not_not]
  exact (prime_dvd_cleared_iff p hp _ d y hN hd).mp
    (zeroHistoryVariable_identically_bad i P hP x p hxi)

/-- A union bound for the complete finite list of numerator checks. These are
the original independent prime priors; no conditioning on history support is
introduced. -/
theorem history_coprimality_removal {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    {n : ℕ} (prime : A → ℕ) (hpInj : Function.Injective prime)
    (hprime : ∀ a, (prime a).Prime)
    (N : I → MvPolynomial (Fin (n + 1)) ℤ) (coord : I → Fin (n + 1))
    (hN : ∀ j, zeroHistoryVariable (coord j) (N j) ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V : ℝ) (β H : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hH : ∀ j, 1 ≤ H j)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hsize : ∀ a, V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ j x, |(integerTestValue (fun a => (prime a : ℤ))
      (zeroHistoryVariable (coord j) (N j)) x : ℝ)| ≤ H j)
    (F : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x, (productPrior μ x : ℂ) *
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ)) (N j) x).natAbs then F x else 0)) -
      ∑ x, (productPrior μ x : ℂ) * F x‖ ≤
      B * ∑ j, (((N j).totalDegree : ℝ) * α + (Real.log (H j) / V) * β j) := by
  let bad (j : I) (x : Fin (n + 1) → A) : Prop :=
    prime (x (coord j)) ∣ (integerTestValue (fun a => (prime a : ℤ)) (N j) x).natAbs
  have hp (x : Fin (n + 1) → A) :
      ‖(if ∀ j, ¬bad j x then F x else 0) - F x‖ ≤
        B * ∑ j, if bad j x then (1 : ℝ) else 0 := by
    by_cases hx : ∀ j, ¬bad j x
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hx)), sub_self, norm_zero]
      exact mul_nonneg hB (Finset.sum_nonneg fun _ _ => by positivity)
    · obtain ⟨j, hj⟩ := not_forall.mp hx
      have hj' : bad j x := Classical.not_not.mp hj
      have hs : (1 : ℝ) ≤ ∑ j, if bad j x then 1 else 0 := by
        simpa only [hj', ite_true] using
          (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
            (show (0 : ℝ) ≤ if bad j x then 1 else 0 by positivity)) (Finset.mem_univ j))
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hx h)), zero_sub, norm_neg]
      exact (hF x).trans (by nlinarith)
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ x, ‖(productPrior μ x : ℂ) *
        ((if ∀ j, ¬bad j x then F x else 0) - F x)‖ := norm_sum_le _ _
    _ = ∑ x, productPrior μ x *
        ‖(if ∀ j, ¬bad j x then F x else 0) - F x‖ := by
      simp only [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (productPrior_nonneg μ hμ _)]
    _ ≤ ∑ x, productPrior μ x * (B * ∑ j, if bad j x then (1 : ℝ) else 0) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (productPrior_nonneg μ hμ x)
    _ = B * ∑ j, ∑ x, productPrior μ x * if bad j x then (1 : ℝ) else 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      ext j
      congr 1
      ext x
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Finset.sum_le_sum
      intro j _
      exact reconstructed_prime_coprimality_error prime hpInj hprime (N j) (coord j) (hN j)
        μ hμ hmass α (β j) V (H j) hα (hβ j) hV (hH j) hmax (hpmax j) hsize (hvalue j)

end Ostmann

end OAI
