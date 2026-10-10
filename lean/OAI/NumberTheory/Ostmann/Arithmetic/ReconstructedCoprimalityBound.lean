import OAI.NumberTheory.Ostmann.Construction.ExpandedHistoryFormula

namespace OAI

/-! # Large-prime support after reconstruction

An identically divisible reconstructed numerator has empty valid support.
Otherwise the original independent prime priors give the polynomial error.
No conditioning of those priors is used in either case. -/

namespace Ostmann

open scoped BigOperators Classical

theorem reconstructed_coprimality_bound
    {A I : Type*} [Fintype A] [Nonempty A] [Fintype I] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → HistoryFormula (Fin (n + 1))) (coord : I → Fin (n + 1))
    (y : I → (Fin (n + 1) → A) → ℤ)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hinputs : ∀ j, (F j).InputsBounded R)
    (W : (Fin (n + 1) → A) → ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ B)
    (hvalid : ∀ x, W x ≠ 0 → ∀ j,
      (F j).value (fun i => (prime (x i) : ℚ)) = y j x ∧
      ¬prime (x (coord j)) ∣ (F j).cleared.denominator.natAbs)
    (hcancel : ‖∑ x, (productPrior μ x : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, (productPrior μ x : ℂ) *
      (if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0)‖ ≤
      δ + B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) := by
  by_cases hz : ∀ j, zeroHistoryVariable (coord j) (F j).cleared.numerator ≠ 0
  · have hgate (x : Fin (n + 1) → A) :
        (if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0) =
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
          then W x else 0) := by
      by_cases hw : W x = 0
      · simp only [hw, ite_self]
      · have hi (j : I) := (F j).cleared.prime_coprime_integer_value
          (fun i => (prime (x i) : ℤ)) (prime (x (coord j))) (hprime _)
          (hvalid x hw j).2 (y j x) (by
            simpa only [HistoryFormula.value, Int.cast_natCast] using (hvalid x hw j).1)
        have hg : (∀ j, (prime (x (coord j))).Coprime (y j x).natAbs) ↔
            (∀ j, ¬prime (x (coord j)) ∣
              (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs) :=
          forall_congr' hi
        simp only [hg]
    simp_rw [hgate]
    let S := ∑ x, (productPrior μ x : ℂ) * W x
    have he := formula_coprimality_removal prime hpInj hprime F coord hz μ hμ hmass
      α V R β hα hβ hV hR hmax hpmax hlower hupper hinputs W B hB hW
    calc
      _ = ‖((∑ x, (productPrior μ x : ℂ) *
            (if ∀ j, ¬prime (x (coord j)) ∣
              (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
              then W x else 0)) - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ ‖(∑ x, (productPrior μ x : ℂ) *
            (if ∀ j, ¬prime (x (coord j)) ∣
              (integerTestValue (fun a => (prime a : ℤ)) (F j).cleared.numerator x).natAbs
              then W x else 0)) - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) + δ :=
        add_le_add he hcancel
      _ = _ := add_comm _ _
  · obtain ⟨j, hj⟩ := not_forall.mp hz
    have hj0 : zeroHistoryVariable (coord j) (F j).cleared.numerator = 0 :=
      Classical.not_not.mp hj
    have hzero (x : Fin (n + 1) → A) :
        (if ∀ k, (prime (x (coord k))).Coprime (y k x).natAbs then W x else 0) = 0 := by
      split_ifs with hg
      · by_contra hw
        have hn := zero_cleared_history_support (F j).cleared.numerator (coord j) hj0
          (fun i => (prime (x i) : ℤ)) (prime (x (coord j))) (hprime _) rfl
          (F j).cleared.denominator (y j x)
          ((F j).cleared.integer_value_cleared _ _ (by
            simpa only [HistoryFormula.value, Int.cast_natCast] using (hvalid x hw j).1))
          (hvalid x hw j).2
        exact hn (hg j)
      · rfl
    simp_rw [hzero, mul_zero]
    rw [Finset.sum_const_zero, norm_zero]
    have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    exact add_nonneg hδ (mul_nonneg hB (Finset.sum_nonneg fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg hα
        (mul_nonneg (div_nonneg hlog hV.le) (hβ j)))))

end Ostmann

end OAI
