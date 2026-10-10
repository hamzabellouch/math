import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyFactorization

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def positiveFrequencyTriples (L B : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((Finset.Icc 1 B) ×ˢ L.divisors) ×ˢ Finset.Icc 1 B).filter
    (fun t => Squarefree t.1.1 ∧ t.1.1.Coprime L ∧ t.1.1 * t.1.2 * t.2 ^ 2 ≤ B)

theorem mem_positiveFrequencyTriples {L B : ℕ} {s v w : ℕ} :
    ((s, v), w) ∈ positiveFrequencyTriples L B ↔
      (1 ≤ s ∧ s ≤ B) ∧ (v ∣ L ∧ L ≠ 0) ∧ (1 ≤ w ∧ w ≤ B) ∧
        Squarefree s ∧ s.Coprime L ∧ s * v * w ^ 2 ≤ B := by
  simp only [positiveFrequencyTriples, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc, Nat.mem_divisors]
  tauto

theorem positive_frequency_parameters_le {s v w : ℕ}
    (hs : 0 < s) (hv : 0 < v) (hw : 0 < w) :
    s ≤ s * v * w ^ 2 ∧ w ≤ s * v * w ^ 2 := by
  constructor
  · simpa only [mul_assoc] using Nat.le_mul_of_pos_right s (mul_pos hv (pow_pos hw 2))
  · have hw2 : w ≤ w ^ 2 := by nlinarith
    exact hw2.trans (Nat.le_mul_of_pos_left (w ^ 2) (mul_pos hs hv))

theorem sum_positive_frequency_triples {A : Type*} [AddCommMonoid A]
    {L : ℕ} (hL : Squarefree L) (B : ℕ) (F : ℕ → A) :
    (∑ u ∈ Finset.Icc 1 B, F u) =
      ∑ t ∈ positiveFrequencyTriples L B, F (t.1.1 * t.1.2 * t.2 ^ 2) := by
  classical
  symm
  apply Finset.sum_bij (fun t _ => t.1.1 * t.1.2 * t.2 ^ 2)
  · rintro ⟨⟨s, v⟩, w⟩ ht
    obtain ⟨hsB, hv, hwB, hs, hc, hprod⟩ := mem_positiveFrequencyTriples.mp ht
    exact Finset.mem_Icc.mpr ⟨mul_pos
      (mul_pos hsB.1 (Nat.pos_of_dvd_of_pos hv.1 (Nat.pos_of_ne_zero hL.ne_zero)))
      (pow_pos hwB.1 2), hprod⟩
  · rintro ⟨⟨s, v⟩, w⟩ hx ⟨⟨t, z⟩, r⟩ hy heq
    obtain ⟨hsB, hv, hwB, hs, hc, hprod⟩ := mem_positiveFrequencyTriples.mp hx
    obtain ⟨htB, hz, hrB, ht, htc, hprod'⟩ := mem_positiveFrequencyTriples.mp hy
    have hu := positive_frequency_factorization_unique hL hs ht hc htc hv.1 hz.1 hwB.1 hrB.1 heq
    exact Prod.ext (Prod.ext hu.1 hu.2.1) hu.2.2
  · intro u hu
    obtain ⟨hu0, huB⟩ := Finset.mem_Icc.mp hu
    obtain ⟨s, v, w, hs, hc, hv, hw, heq⟩ := exists_positive_frequency_factorization hL hu0
    have hp := positive_frequency_parameters_le (Nat.pos_of_ne_zero hs.ne_zero)
      (Nat.pos_of_dvd_of_pos hv (Nat.pos_of_ne_zero hL.ne_zero)) hw
    have hprod : s * v * w ^ 2 ≤ B := heq ▸ huB
    refine ⟨((s, v), w), ?_, heq.symm⟩
    exact mem_positiveFrequencyTriples.mpr
      ⟨⟨Nat.pos_of_ne_zero hs.ne_zero, hp.1.trans hprod⟩, ⟨hv, hL.ne_zero⟩,
        ⟨hw, hp.2.trans hprod⟩, hs, hc, hprod⟩
  · intro t ht
    rfl

theorem sum_positive_frequency_nested {A : Type*} [AddCommMonoid A]
    {L : ℕ} (hL : Squarefree L) (B : ℕ) (F : ℕ → A) :
    (∑ u ∈ Finset.Icc 1 B, F u) =
      ∑ s ∈ (Finset.Icc 1 B).filter (fun s => Squarefree s ∧ s.Coprime L),
        ∑ v ∈ L.divisors,
          ∑ w ∈ (Finset.Icc 1 B).filter (fun w => s * v * w ^ 2 ≤ B), F (s * v * w ^ 2) := by
  rw [sum_positive_frequency_triples hL B F]
  simp only [positiveFrequencyTriples, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsc : Squarefree s ∧ s.Coprime L
  · rw [ite_eq_left hsc]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hcut : s * v * w ^ 2 ≤ B
    · rw [ite_eq_left ⟨hsc.1, hsc.2, hcut⟩, ite_eq_left hcut]
    · rw [ite_eq_right (fun h => hcut h.2.2), ite_eq_right hcut]
  · have hs : ¬Squarefree s ∨ ¬s.Coprime L := not_and_or.mp hsc
    rcases hs with hs | hs <;> simp [hs]

end Ostmann.QuadraticCenter

end

end OAI
