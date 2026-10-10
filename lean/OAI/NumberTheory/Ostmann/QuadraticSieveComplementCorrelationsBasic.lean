import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorCorrelation
import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingCorrelations
import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingIntegral

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate MeasureTheory Set
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def complementaryPair (S : Finset ℕ) (a : ℕ → ℂ) (F : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then a n * conj (a t) * F (n*t) else 0

noncomputable def complementaryCorrelation (W : 𝓢(ℝ, ℂ)) (M : ℝ) (K Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  complementaryPair S a (complementarySchwartzSum W M K Δ)

noncomputable def complementaryCorrelationMain (W : 𝓢(ℝ, ℂ)) (M : ℝ) (K Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (X₁ X₂ L : ℕ → ℝ) : ℂ :=
  complementaryPair S a (fun q => complementaryPoissonMain W M K Δ q X₁ X₂ L)

theorem complementaryPair_add (S : Finset ℕ) (a F G : ℕ → ℂ) :
    complementaryPair S a (fun q => F q + G q) =
      complementaryPair S a F + complementaryPair S a G := by
  simp only [complementaryPair, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

theorem complementaryPair_sub (S : Finset ℕ) (a F G : ℕ → ℂ) :
    complementaryPair S a (fun q => F q - G q) =
      complementaryPair S a F - complementaryPair S a G := by
  simp only [complementaryPair, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

theorem complementaryPair_mul (S : Finset ℕ) (a F : ℕ → ℂ) (z : ℂ) :
    complementaryPair S a (fun q => z * F q) = z * complementaryPair S a F := by
  simp only [complementaryPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

theorem complementaryPair_sum {ι : Type*} (V : Finset ι) (S : Finset ℕ)
    (a : ℕ → ℂ) (F : ι → ℕ → ℂ) :
    complementaryPair S a (fun q => ∑ v ∈ V, F v q) =
      ∑ v ∈ V, complementaryPair S a (F v) := by
  classical
  have heq (n t : ℕ) :
      (if Nat.Coprime n t then a n * conj (a t) * (∑ v ∈ V, F v (n*t)) else 0) =
        ∑ v ∈ V, if Nat.Coprime n t then a n * conj (a t) * F v (n*t) else 0 := by
    by_cases hc : Nat.Coprime n t
    · simp only [ite_eq_left hc, Finset.mul_sum]
    · simp only [ite_eq_right hc, Finset.sum_const_zero]
  simp only [complementaryPair, heq]
  calc
    _ = ∑ n ∈ S, ∑ v ∈ V, ∑ t ∈ S,
        if Nat.Coprime n t then a n * conj (a t) * F v (n*t) else 0 :=
      Finset.sum_congr rfl (fun n hn => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem complementaryPair_ite (S : Finset ℕ) (a F : ℕ → ℂ) (P : Prop) [Decidable P] :
    complementaryPair S a (fun q => if P then F q else 0) =
      if P then complementaryPair S a F else 0 := by
  by_cases h : P <;> simp [h, complementaryPair]

theorem complementaryPair_leading (M : ℝ) (I : ℂ) (K Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v Δ then
      complementaryPair S a (fun q => I * (Real.sqrt (M/v) : ℂ) *
        ((Nat.totient (2*q*Δ) : ℂ) / (2*q*Δ : ℕ)) * (jacobiSym (v : ℤ) q : ℂ)) else 0) =
      complementLeadingCorrelation M I K Δ S a := by
  unfold complementLeadingCorrelation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : Nat.Coprime v Δ
  · simp only [ite_eq_left hc, complementaryPair]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hnt : Nat.Coprime n t
    · rw [ite_eq_left hnt, ite_eq_left (show Nat.Coprime n t ∧ Nat.Coprime v Δ from ⟨hnt,hc⟩)]
      ring
    · rw [ite_eq_right hnt, ite_eq_right (show ¬ (Nat.Coprime n t ∧ Nat.Coprime v Δ) from fun h => hnt h.1)]
      ring
  · simp only [hc, and_false, ite_false, Finset.sum_const_zero, mul_zero]

theorem complementaryPair_divisors (S : Finset ℕ) (a : ℕ → ℂ)
    (N Δ v : ℕ) (F : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N ∧ Nat.Coprime (2*Δ) n) :
    complementaryPair S a (fun q => (jacobiSym (v : ℤ) q : ℂ) *
      ∑ d ∈ (2*q*Δ).divisors, (μ d : ℂ) * F d) =
      ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2),
        (μ r : ℂ) * (μ d : ℂ) * F (r*d) *
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v : ℤ) := by
  have heq (q : ℕ) : 2*q*Δ = (2*Δ)*q := by ring
  simp_rw [heq]
  simpa only [complementaryPair, mul_assoc] using
    coprime_fixed_divisor_correlation_exchange S S a (fun n => conj (a n)) N (2*Δ)
      (v : ℤ) F hS hS

end Ostmann.QuadraticSieve

end OAI
