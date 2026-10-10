import OAI.NumberTheory.Ostmann.Construction.FiniteFormulaRenaming
import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedPrior

namespace OAI

namespace Ostmann

open scoped BigOperators Classical

theorem finite_reconstructed_coprimality_bound
    {A I K : Type*} [Fintype A] [Nonempty A] [Fintype I] [Fintype K] [Nonempty K]
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (F : I → HistoryFormula (K)) (coord : I → K)
    (y : I → (K → A) → ℤ)
    (μ : K → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j)
    (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hinputs : ∀ j, (F j).InputsBounded R)
    (W : (K → A) → ℂ) (B δ : ℝ)
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hW : ∀ x, ‖W x‖ ≤ B)
    (hvalid : ∀ x, W x ≠ 0 → ∀ j,
      (F j).value (fun i => (prime (x i) : ℚ)) = y j x ∧
      ¬prime (x (coord j)) ∣ (F j).cleared.denominator.natAbs)
    (hcancel : ‖∑ x, ((∏ i, μ i (x i) : ℝ) : ℂ) * W x‖ ≤ δ) :
    ‖∑ x, ((∏ i, μ i (x i) : ℝ) : ℂ) *
      (if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0)‖ ≤
      δ + B * ∑ j, ((F j).cost : ℝ) * (α + Real.log R / V * β j) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := K))
  let e : Fin (m + 1) ≃ K := (finCongr hm.symm).trans (Fintype.equivFin K).symm
  have hv (x : Fin (m + 1) → A) (hx : W (x ∘ e.symm) ≠ 0) (j : I) :
      ((F j).rename e.symm).value (fun i => (prime (x i) : ℚ)) = y j (x ∘ e.symm) ∧
      ¬prime (x (e.symm (coord j))) ∣ ((F j).rename e.symm).cleared.denominator.natAbs := by
    have h := hvalid (x ∘ e.symm) hx j
    simpa only [HistoryFormula.rename_value, HistoryFormula.rename_denominator,
      Function.comp_def] using h
  have hb : ‖∑ x : Fin (m + 1) → A, (productPrior (fun i => μ (e i)) x : ℂ) *
      W (x ∘ e.symm)‖ ≤ δ := by
    simp only [productPrior]
    apply Eq.trans_le (congrArg norm ?_) hcancel
    convert finite_prior_reindex e μ W using 1
    with_reducible exact finite_enumeration_sum _ _ _
  have hh := reconstructed_coprimality_bound prime hpInj hprime
    (fun j => (F j).rename e.symm) (fun j => e.symm (coord j))
    (fun j x => y j (x ∘ e.symm)) (fun i => μ (e i))
    (fun i a => hμ (e i) a) (fun i => hmass (e i))
    α V R β hα hβ hV hR (fun i a => hmax (e i) a)
    (by intro j a; simpa only [Equiv.apply_symm_apply] using hpmax j a)
    hlower hupper (fun j => (F j).rename_inputs e.symm R (hinputs j))
    (fun x => W (x ∘ e.symm)) B δ hB hδ (fun x => hW (x ∘ e.symm)) hv hb
  simp only [HistoryFormula.rename_cost, productPrior] at hh
  have he := finite_prior_reindex e μ (fun x =>
    if ∀ j, (prime (x (coord j))).Coprime (y j x).natAbs then W x else 0)
  simp only [Function.comp_apply] at he
  apply Eq.trans_le (congrArg norm ?_) hh
  symm
  convert he using 1
  with_reducible exact finite_enumeration_sum _ _ _

end Ostmann

end OAI
