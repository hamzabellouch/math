import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsBasic

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap

noncomputable def dualCorrelation (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  complementaryPair S a (fun q => ∑' m : ℤ, if Nat.Coprime m.natAbs (2*Δ) then
    (jacobiSym m q : ℂ) * W ((m : ℝ)/M) else 0)

noncomputable def dualCorrelationMain (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  complementaryPair S a (fun q => dualCorrelationMainTerm W M Δ K q X₁ X₂ L)

noncomputable def dualCorrelationTail (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ : ℕ) (K : ℝ)
    (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  complementaryPair S a (fun q => dualCorrelationTailTerm W M Δ q K)

noncomputable def dualCorrelationRemainder (W : 𝓢(ℝ, ℂ)) (M : ℝ) (Δ K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℕ → ℝ) : ℂ :=
  complementaryPair S a (fun q => dualCorrelationRemainderTerm W M Δ K q X₁ X₂ L)

theorem complementaryPair_congr (S : Finset ℕ) (a F G : ℕ → ℂ)
    (h : ∀ n ∈ S, ∀ t ∈ S, Nat.Coprime n t → F (n*t) = G (n*t)) :
    complementaryPair S a F = complementaryPair S a G := by
  unfold complementaryPair
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hc : Nat.Coprime n t
  · rw [ite_eq_left hc, ite_eq_left hc, h n hn t ht hc]
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem dualCorrelation_eq (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ)
    (hΔ : Δ ≠ 0) (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℕ → ℝ)
    (hS : S ⊆ oddSquarefreeUpTo N) (hS1 : ∀ n ∈ S, 1 < n) :
    dualCorrelation W M Δ S a = dualCorrelationMain W M Δ K S a X₁ X₂ L +
      dualCorrelationRemainder W M Δ K S a X₁ X₂ L + dualCorrelationTail W M Δ K S a := by
  rw [dualCorrelation, dualCorrelationMain, dualCorrelationRemainder, dualCorrelationTail,
    ← complementaryPair_add, ← complementaryPair_add]
  apply complementaryPair_congr
  intro n hn t ht hcop
  obtain ⟨hnp, hnb, hno, hns⟩ := mem_oddSquarefreeUpTo.mp (hS hn)
  obtain ⟨htp, htb, hto, hts⟩ := mem_oddSquarefreeUpTo.mp (hS ht)
  let : NeZero (n*t) := ⟨(Nat.mul_pos hnp htp).ne'⟩
  exact coprime_quadratic_poisson_second_main (hno.mul hto)
    (Nat.squarefree_mul_iff.mpr ⟨hcop,hns,hts⟩) (by nlinarith [hS1 n hn]) W M hM Δ K hΔ X₁ X₂ L

end Ostmann.QuadraticSieve

end OAI
