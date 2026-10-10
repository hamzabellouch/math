import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsError

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap

noncomputable def dualPairErrorScale (S : Finset ℕ) (a : ℕ → ℂ) (B : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then ‖a n‖ * ‖a t‖ * B (n*t) else 0

theorem norm_complementaryPair_le_weighted (S : Finset ℕ) (a F : ℕ → ℂ)
    (B : ℕ → ℝ) (C : ℝ)
    (hF : ∀ n ∈ S, ∀ t ∈ S, Nat.Coprime n t → ‖F (n*t)‖ ≤ C * B (n*t)) :
    ‖complementaryPair S a F‖ ≤ C * dualPairErrorScale S a B := by
  calc
    _ ≤ ∑ n ∈ S, ∑ t ∈ S,
        ‖if Nat.Coprime n t then a n * conj (a t) * F (n*t) else 0‖ := by
      unfold complementaryPair
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => norm_sum_le _ _))
    _ ≤ ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then
        ‖a n‖ * ‖a t‖ * (C * B (n*t)) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro t ht
      by_cases hc : Nat.Coprime n t
      · rw [ite_eq_left hc, ite_eq_left hc, norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hF n hn t ht hc) (by positivity)
      · rw [ite_eq_right hc, ite_eq_right hc, norm_zero]
    _ = _ := by
      simp only [dualPairErrorScale, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      split_ifs <;> ring

noncomputable def dualFirstErrorScale (M : ℝ) (Δ q A : ℕ) (K : ℝ) : ℝ :=
  ∑ e ∈ (2*Δ).divisors, (M/(e*q))*Real.sqrt (q : ℝ) /
    ((M/(e*q))^(A+2)*K^A)

theorem dualCorrelationTail_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M K : ℝ) (Δ N : ℕ), 0 < M → 0 < K → Δ ≠ 0 →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      ‖dualCorrelationTail W M Δ K S a‖ ≤
        C * dualPairErrorScale S a (fun q => dualFirstErrorScale M Δ q A K) := by
  obtain ⟨C,hC,hbound⟩ := dualPoissonTail_bound W A
  refine ⟨C,hC,?_⟩
  intro M K Δ N hM hK hΔ S a hS
  unfold dualCorrelationTail
  apply norm_complementaryPair_le_weighted
  intro n hn t ht hcop
  obtain ⟨hnp,hnb,hno,hns⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
  obtain ⟨htp,htb,hto,hts⟩ := mem_oddSquarefreeUpTo.mp (hS ht)
  let : NeZero (n*t) := ⟨(Nat.mul_pos hnp htp).ne'⟩
  rw [dualCorrelationTailTerm_eq]
  exact hbound M (2*Δ) (n*t) K hM (mul_ne_zero (by omega) hΔ) (hno.mul hto)
    (Nat.squarefree_mul_iff.mpr ⟨hcop,hns,hts⟩) hK

theorem dualCorrelationRemainder_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (Δ K N : ℕ), 0 < M →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, 1 < n) →
      ∀ (X₁ X₂ J L : ℕ → ℕ → ℝ),
      (∀ n ∈ S, ∀ t ∈ S, Nat.Coprime n t →
        ∀ e ∈ (2*Δ).divisors, ∀ b ∈ oddSquarefreeUpTo K,
          0 < X₁ e b ∧ X₁ e b ≤ Real.sqrt ((e : ℝ)*(n*t)/(M*b)) ∧
          Real.sqrt ((e : ℝ)*(n*t)/(M*b)) ≤ X₂ e b ∧ 0 < J e b ∧
          J e b ≤ min (Real.sqrt ((e : ℝ)*(n*t)/(M*b))/X₁ e b)
            (X₂ e b/Real.sqrt ((e : ℝ)*(n*t)/(M*b))) ∧
          (X₂ e b/Real.sqrt ((e : ℝ)*(n*t)/(M*b)))^2 ≤ L e b) →
      ‖dualCorrelationRemainder W M Δ K S a X₁ X₂ L‖ ≤
        C * dualPairErrorScale S a (fun q => dualSecondErrorScale M Δ K q A J) := by
  obtain ⟨C,hC,hbound⟩ := dualCorrelationRemainderTerm_bound W A
  refine ⟨C,hC,?_⟩
  intro M Δ K N hM S a hS hS1 X₁ X₂ J L hp
  unfold dualCorrelationRemainder
  apply norm_complementaryPair_le_weighted
  intro n hn t ht hcop
  obtain ⟨hnp,hnb,hno,hns⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
  obtain ⟨htp,htb,hto,hts⟩ := mem_oddSquarefreeUpTo.mp (hS ht)
  let : NeZero (n*t) := ⟨(Nat.mul_pos hnp htp).ne'⟩
  apply hbound M Δ K (n*t) hM (hno.mul hto) (Nat.squarefree_mul_iff.mpr ⟨hcop,hns,hts⟩)
    (by nlinarith [hS1 n hn]) X₁ X₂ J L
  simpa only [Nat.cast_mul] using hp n hn t ht hcop

end Ostmann.QuadraticSieve

end OAI
