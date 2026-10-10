import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveModel

namespace OAI

/-! Finite interval errors for the periodic congruence classes in the sieve. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma count_periodic_blocks (d : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ P (n%d)) (q r : ℕ) :
    Nat.count P (q*d+r) = q*Nat.count P d+Nat.count P r := by
  have hshift (q : ℕ) : (fun k => P (q*d+k)) = P := by
    funext k
    apply propext
    rw [hP (q*d+k)]
    simp only [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_mod]
    exact (hP k).symm
  have hblocks : Nat.count P (q*d)=q*Nat.count P d := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul,Nat.count_add,ih]
      simp only [hshift]
      ring
  rw [Nat.count_add,hblocks]
  simp only [hshift]

lemma count_periodic_error (d : ℕ) (hd : 0 < d) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P n ↔ P (n%d)) (N : ℕ) :
    |(Nat.count P N:ℝ)-(N:ℝ)/d*(Nat.count P d:ℝ)| ≤ d := by
  have hsplit : N=(N/d)*d+N%d := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N d).symm
  have hc : Nat.count P N=(N/d)*Nat.count P d+Nat.count P (N%d) := by
    conv_lhs => rw [hsplit]
    exact count_periodic_blocks d P hP (N/d) (N%d)
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hr : ((N%d:ℕ):ℝ) ≤ d := by exact_mod_cast (Nat.mod_lt N hd).le
  have htail : (Nat.count P (N%d):ℝ) ≤ ((N%d:ℕ):ℝ) := by exact_mod_cast Nat.count_le P
  have hmass : (Nat.count P d:ℝ) ≤ d := by exact_mod_cast Nat.count_le P
  have hfrac : ((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) ≤ ((N%d:ℕ):ℝ) := by
    calc
      _ ≤ ((N%d:ℕ):ℝ)/d*d := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := div_mul_cancel₀ _ hdR.ne'
  have hid : (Nat.count P N:ℝ)-(N:ℝ)/d*(Nat.count P d:ℝ) =
      (Nat.count P (N%d):ℝ)-((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) := by
    rw [hc]
    push_cast
    have hNr : (N:ℝ)=(N/d:ℕ)* (d:ℝ)+(N%d:ℕ) := by exact_mod_cast hsplit
    rw [hNr]
    field_simp
    ring
  rw [hid]
  apply abs_le.mpr
  constructor
  · have hnon : (0:ℝ) ≤ Nat.count P (N%d) := Nat.cast_nonneg _
    linarith
  · have hnon : (0:ℝ) ≤ ((N%d:ℕ):ℝ)/d*(Nat.count P d:ℝ) := by positivity
    linarith

lemma shiftedSievePolynomial_mod (b d q : ℕ) :
    shiftedSievePolynomial b q % d = shiftedSievePolynomial b (q%d) % d := by
  simp [shiftedSievePolynomial,Nat.add_mod,Nat.mul_mod]

lemma shiftedSieve_count_error (b d : ℕ) (hd : 0 < d) (N : ℕ) :
    |(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) N:ℝ)-
      (N:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ)| ≤ d := by
  apply count_periodic_error d hd
  intro q
  simp only [Nat.dvd_iff_mod_eq_zero,shiftedSievePolynomial_mod b d q]
lemma interval_count_discrepancy (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    |(((Finset.Icc 1 N).filter P).card:ℝ)-(Nat.count P N:ℝ)| ≤ 1 := by
  have hupper : ((Finset.Icc 1 N).filter P).card ≤ Nat.count P N+1 := by
    have hs : (Finset.Icc 1 N).filter P ⊆ (Finset.range (N+1)).filter P := by
      intro n hn
      obtain ⟨hn,hP⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hn).2; omega),hP⟩
    have hh := Finset.card_le_card hs
    rw [← Nat.count_eq_card_filter_range,Nat.count_succ] at hh
    split_ifs at hh <;> omega
  have hlower : Nat.count P N ≤ ((Finset.Icc 1 N).filter P).card+1 := by
    have hs : (Finset.range N).filter P ⊆ insert 0 ((Finset.Icc 1 N).filter P) := by
      intro n hn
      obtain ⟨hn,hP⟩ := Finset.mem_filter.mp hn
      by_cases hz : n=0
      · simp [hz]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨by omega,by have := Finset.mem_range.mp hn; omega⟩,hP⟩
    have hh := (Finset.card_le_card hs).trans (Finset.card_insert_le 0 _)
    rwa [← Nat.count_eq_card_filter_range] at hh
  have hu : (((Finset.Icc 1 N).filter P).card:ℝ) ≤ (Nat.count P N:ℝ)+1 := by exact_mod_cast hupper
  have hl : (Nat.count P N:ℝ) ≤ (((Finset.Icc 1 N).filter P).card:ℝ)+1 := by exact_mod_cast hlower
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma shiftedSieve_interval_error (b d : ℕ) (hd : 0 < d) (N : ℕ) :
    |(((Finset.Icc 1 N).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ)-
      (N:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ)| ≤ d+1 := by
  calc
    _ ≤ |(((Finset.Icc 1 N).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ)-
        (Nat.count (fun q => d ∣ shiftedSievePolynomial b q) N:ℝ)|+
      |(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) N:ℝ)-
        (N:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ)| := abs_sub_le _ _ _
    _ ≤ 1+d := add_le_add (interval_count_discrepancy _ N) (shiftedSieve_count_error b d hd N)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
