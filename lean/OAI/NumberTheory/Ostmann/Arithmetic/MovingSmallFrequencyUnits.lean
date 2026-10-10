import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullSupport

namespace OAI

/-! # The small-prime frequency tests follow from the actual range separation -/

namespace Ostmann

theorem MovingSlotData.Frequencies.mono {σ : Type*} {P Q : ℤ → Prop}
    {n : ℕ} {T : MovingSlotData σ n} (h : T.Frequencies P) (hPQ : ∀ s, P s → Q s) :
    T.Frequencies Q := by
  induction T with
  | leaf => exact hPQ _ h
  | node s CL CR U left right ihL ihR => exact ⟨hPQ s h.1, ihL h.2.1, ihR h.2.2⟩

theorem small_prime_frequency_unit (p : ℕ) (hp : p.Prime) (s : ℤ)
    (hs : s ≠ 0) (hsp : s.natAbs < p) : IsCoprime s (p : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]
  exact (hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hs) hsp)).symm

theorem MovingSlotData.small_frequency_units {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hV : T.Frequencies (fun s => s.natAbs ≤ V)) :
    ∀ i, T.Frequencies (fun s => IsCoprime s (value i : ℤ)) := by
  intro i
  induction T with
  | leaf s regular => exact small_prime_frequency_unit (value i) (hprime i) s hf (hV.trans_lt (hlarge i))
  | node s CL CR U left right ihL ihR =>
    exact ⟨small_prime_frequency_unit (value i) (hprime i) s hf.1 (hV.1.trans_lt (hlarge i)),
      ihL hf.2.1 hV.2.1, ihR hf.2.2 hV.2.2⟩

theorem MovingSlotData.small_frequency_residues {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) (V : ℕ) (hlarge : ∀ i, V < value i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (hV : T.Frequencies (fun s => s.natAbs ≤ V)) :
    ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0) := by
  intro i
  let : Fact (value i).Prime := ⟨hprime i⟩
  apply (T.small_frequency_units value hprime V hlarge hf hV i).mono
  intro s hs
  have hu : IsUnit (s : ZMod (value i)) := by
    apply isCoprime_zero_right.mp
    simpa only [Int.cast_natCast, ZMod.natCast_self] using hs.intCast (R := ZMod (value i))
  exact hu.ne_zero

end Ostmann

end OAI
