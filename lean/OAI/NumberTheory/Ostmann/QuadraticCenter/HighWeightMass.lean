import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightDivisor
import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightResidueCount

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem weighted_divisor_overcount (S R : Finset ℕ) (F G : ℕ → ℝ)
    (hG : ∀ r ∈ R, 0 ≤ G r)
    (hcover : ∀ n ∈ S, ∃ r ∈ R, r ∣ n ∧ F n ≤ G r) :
    (∑ n ∈ S, F n) ≤ ∑ r ∈ R, ((S.filter (fun n => r ∣ n)).card : ℝ) * G r := by
  classical
  calc
    _ ≤ ∑ n ∈ S, ∑ r ∈ R, if r ∣ n then G r else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨r, hr, hrd, hweight⟩ := hcover n hn
      apply hweight.trans
      calc
        G r = if r ∣ n then G r else 0 := by simp only [ite_eq_left hrd]
        _ ≤ _ := Finset.single_le_sum
          (f := fun r => if r ∣ n then G r else 0)
          (fun r hr => by
            split_ifs
            · exact hG r hr
            · exact le_rfl) hr
    _ = ∑ r ∈ R, ∑ n ∈ S, if r ∣ n then G r else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

noncomputable def highWeightHalfDivisors (X L k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * X + 1)).filter (fun r =>
    Squarefree r ∧ r.Coprime L ∧ r ^ 2 ≤ 2 * X ∧ k ≤ r.primeFactors.card)

@[simp] theorem mem_highWeightHalfDivisors {X L k r : ℕ} :
    r ∈ highWeightHalfDivisors X L k ↔
      r ≤ 2 * X ∧ Squarefree r ∧ r.Coprime L ∧ r ^ 2 ≤ 2 * X ∧ k ≤ r.primeFactors.card := by
  simp only [highWeightHalfDivisors, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem high_weight_half_divisor_cover (S : Finset ℕ) {X L k : ℕ}
    (hS : ∀ n ∈ S, Squarefree n) (hcop : ∀ n ∈ S, n.Coprime L)
    (hupper : ∀ n ∈ S, n ≤ 2 * X) (hweight : ∀ n ∈ S, 2 * k ≤ n.primeFactors.card)
    {u : ℝ} (hu : 1 ≤ u) :
    ∀ n ∈ S, ∃ r ∈ highWeightHalfDivisors X L k,
      r ∣ n ∧ u ^ n.primeFactors.card ≤ u * (u ^ 2) ^ r.primeFactors.card := by
  intro n hn
  obtain ⟨r, hrd, hrs, hrc, hr2, hrω, hru⟩ :=
    exists_coprime_half_divisor_weight (hS n hn) (hcop n hn) hu
  refine ⟨r, mem_highWeightHalfDivisors.mpr ⟨?_, hrs, hrc, hr2.trans (hupper n hn), ?_⟩,
    hrd, hru⟩
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (hS n hn).ne_zero) hrd).trans (hupper n hn)
  · have hw := hweight n hn
    omega

theorem high_weight_mass_le_half_divisor_sum (S : Finset ℕ) {X L a k : ℕ}
    (hL : 0 < L) (hX : 2 * L ^ 2 ≤ X)
    (hS : ∀ n ∈ S, Squarefree n) (hcop : ∀ n ∈ S, n.Coprime L)
    (hres : ∀ n ∈ S, Nat.ModEq L n a)
    (hupper : ∀ n ∈ S, n ≤ 2 * X) (hweight : ∀ n ∈ S, 2 * k ≤ n.primeFactors.card)
    {u : ℝ} (hu : 1 ≤ u) :
    (∑ n ∈ S, u ^ n.primeFactors.card) ≤
      (3 * u * (X : ℝ) / (L : ℝ)) *
        ∑ r ∈ highWeightHalfDivisors X L k, (u ^ 2) ^ r.primeFactors.card / (r : ℝ) := by
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  apply (weighted_divisor_overcount S (highWeightHalfDivisors X L k)
    (fun n => u ^ n.primeFactors.card) (fun r => u * (u ^ 2) ^ r.primeFactors.card)
    (fun r hr => by positivity) (high_weight_half_divisor_cover S hS hcop hupper hweight hu)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  obtain ⟨hrX, hrs, hrc, hr2, hrω⟩ := mem_highWeightHalfDivisors.mp hr
  have hcount := coprime_residue_multiple_card_real_le (S.filter (fun n => r ∣ n))
    hL (Nat.pos_of_ne_zero hrs.ne_zero) hrc.symm
    (fun n hn => hres n (Finset.mem_filter.mp hn).1)
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => hupper n (Finset.mem_filter.mp hn).1)
    (half_divisor_density hr2 hX)
  calc
    _ ≤ (3 * (X : ℝ) / ((L : ℝ) * r)) * (u * (u ^ 2) ^ r.primeFactors.card) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end Ostmann.QuadraticCenter

end OAI
