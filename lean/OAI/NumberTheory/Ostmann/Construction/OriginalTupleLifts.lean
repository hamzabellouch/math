import OAI.NumberTheory.Ostmann.Construction.OriginalOffWitnessMoment
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWitnessLift
import OAI.NumberTheory.Ostmann.Construction.PrimeTupleAverages
import OAI.NumberTheory.Ostmann.Construction.PrimeProductTranslations

namespace OAI

/-! # Original Fourier witnesses give a positive family of integer tuple lifts -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap Classical

theorem int_mem_symmetric_Ico_of_abs_le (n : ℤ) (H : ℕ)
    (hn : |(n : ℝ)| ≤ H) : n ∈ Finset.Ico (-(H : ℤ)) (H + 1) := by
  have hh := abs_le.mp hn
  apply Finset.mem_Ico.mpr
  constructor
  · exact_mod_cast hh.1
  · have h : n ≤ (H : ℤ) := by exact_mod_cast hh.2
    omega

/-- Apply the inverse phase theorem to the literal small-kernel event. -/
theorem eventual_original_tuple_witness_lift (B : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hB : 3 ≤ B) (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (k N : ℕ) (t τ : ℕ → ℤ) (h₀ : ℕ → ℕ) (X : ℝ),
      0 < X → (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) →
      (Q.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ m ∈ primeSubsetProducts P k,
        Real.exp (10 * T) ≤ (m : ℝ) / X ∧ (m : ℝ) / X ≤ Real.exp (14 * T) ∧
        ∀ p ∈ m.primeFactors, (p : ℤ) ∣ τ m - t p) →
      ∀ e : Fin k ↪ P,
        principalSmallWitness Q hQ D (primeTupleProduct P e) N (h₀ (primeTupleProduct P e))
          ((τ (primeTupleProduct P e) : ℝ) / primeTupleProduct P e)
          ((primeTupleProduct P e : ℝ) / X) Φ →
        ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
          ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
            (⌈X * Real.exp (13 * T / 100)⌉₊ + 1),
            ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  filter_upwards [eventual_quadratic_witness_lift B Φ hB hΦ] with T hw
  intro Q hQ D P hP k N t τ h₀ X hX hL hK hrange e he
  have heP := primeTupleProduct_mem P e
  obtain ⟨hRlo, hRhi, ht⟩ := hrange _ heP
  obtain ⟨s, hs, V, hV, U, hU, hval⟩ := he
  have hs' := smallSquarefreeKernels_spec Q.toList.prod N s hs
  obtain ⟨a, ha, n, hn, hd⟩ := hw Q hQ D P hP k e t (τ (primeTupleProduct P e))
    (h₀ (primeTupleProduct P e)) X hX hL hK hRlo hRhi
    (fun i => ht _ (primeTuple_member_primeFactors P hP e i))
    ⟨U, V, Finset.mem_powerset.mp hU, Finset.mem_powerset.mp hV,
      s, hs'.1, hs'.2.2.2.2, by simpa only [mul_comm] using hval⟩
  exact ⟨a, ha, n, int_mem_symmetric_Ico_of_abs_le n _ (hn.trans (Nat.le_ceil _)), hd⟩

noncomputable def tupleLiftFamily (P : Finset ℕ) (k A H : ℕ) (t : ℕ → ℤ) : Finset (Fin k ↪ P) :=
  Finset.univ.filter fun e => ∃ a ∈ Finset.Icc 1 A, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
    ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1

theorem primeTuple_event_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (E : ℕ → Prop) [DecidablePred E] :
    (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ *
      ((Finset.univ : Finset (Fin k ↪ P)).filter (fun e => E (primeTupleProduct P e))).card =
      (P.card.choose k : ℝ)⁻¹ * ((primeSubsetProducts P k).filter E).card := by
  have hh := primeTuple_uniform_mean P hP k (fun m => if E m then (1 : ℝ) else 0)
  simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

theorem tupleLiftFamily_probability (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k A H : ℕ) (t : ℕ → ℤ) (E : ℕ → Prop) [DecidablePred E]
    (hlift : ∀ e : Fin k ↪ P, E (primeTupleProduct P e) →
      ∃ a ∈ Finset.Icc 1 A, ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1) :
    (P.card.choose k : ℝ)⁻¹ * ((primeSubsetProducts P k).filter E).card ≤
      (Fintype.card (Fin k ↪ P) : ℝ)⁻¹ * (tupleLiftFamily P k A H t).card := by
  rw [← primeTuple_event_probability P hP k E]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlift e (Finset.mem_filter.mp he).2⟩

end Ostmann

end OAI
