import OAI.NumberTheory.TotientAsymptotic.PrimeWindow

namespace OAI

/-! Exact largest-prime fibers and the negligible lower cutoff. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def shiftedPrimeSet (x t : ℝ) (D : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊1+t/D⌋₊).filter (fun p : ℕ => x^(9/10 : ℝ) ≤ p)

lemma mem_shiftedPrimeSet {x t : ℝ} {D p : ℕ} (ht : 0 ≤ t) (hD : 0 < D) :
    p ∈ shiftedPrimeSet x t D ↔
      p.Prime ∧ x^(9/10 : ℝ) ≤ p ∧ ((p-1 : ℕ)*D : ℕ) ≤ t := by
  have hD0 : (0 : ℝ)<D := by exact_mod_cast hD
  have hy : 0 ≤ 1+t/D := by positivity
  simp only [shiftedPrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpy,hp⟩,hlo⟩
    refine ⟨hp,hlo,?_⟩
    have hh : (p : ℝ) ≤ 1+t/D := (by exact_mod_cast hpy : (p : ℝ)≤⌊1+t/D⌋₊).trans (Nat.floor_le hy)
    have hp1 : 1 ≤ p := hp.one_lt.le
    push_cast
    rw [Nat.cast_sub hp1]
    have := (le_div_iff₀ hD0).mp (show (p : ℝ)-1 ≤ t/D by linarith)
    simpa only [Nat.cast_one] using this
  · rintro ⟨hp,hlo,hv⟩
    have hv' : ((p : ℝ)-1)*D ≤ t := by simpa only [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one] using hv
    have hh : (p : ℝ) ≤ 1+t/D := by
      have := (le_div_iff₀ hD0).mpr hv'
      linarith
    exact ⟨⟨Nat.le_floor hh,hp⟩,hlo⟩

lemma tuple_fiber_eq_shiftedPrimeSet {x t : ℝ} {H : ℕ}
    (hPH : P H ≤ H) (ht : 0 ≤ t) {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    ((tupleFinset x H t).filter (fun τ => τ.tail=ζ)).card =
      (shiftedPrimeSet x t (prefixDenominator ζ)).card := by
  rw [tuple_fiber_card, ite_eq_left hζ]
  congr 1
  ext p
  rw [Finset.mem_filter, mem_shiftedPrimeSet (D := prefixDenominator ζ) ht (basic_prefix_denominator_pos hPH hζ)]
  constructor
  · rintro ⟨_,hp,hlo,hv⟩
    exact ⟨hp,hlo,by simpa only [tupleValue_eq_head, prefixDenominator] using hv⟩
  · rintro ⟨hp,hlo,hv⟩
    have hb : IsBasicTuple x H t ⟨p,ζ⟩ := ⟨hp,hlo,hζ,by
      simpa only [tupleValue_eq_head, prefixDenominator] using hv⟩
    exact ⟨Finset.mem_range.mpr (basic_tuple_head_bound hPH hb), hp,hlo,hb.2.2.2⟩

lemma shiftedPrimeSet_cutoff_error {x : ℝ} (hx : 0 ≤ x) (t : ℝ) (D : ℕ) :
    |((shiftedPrimeSet x t D).card : ℝ)-(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)| ≤
      x^(9/10 : ℝ)+1 := by
  let P := Nat.primesLE ⌊1+t/D⌋₊
  let E := P.filter (fun p : ℕ => ¬ x^(9/10 : ℝ) ≤ p)
  have he : E.card ≤ ⌊x^(9/10 : ℝ)⌋₊+1 := by
    apply (Finset.card_le_card (t := Finset.range (⌊x^(9/10 : ℝ)⌋₊+1)) ?_).trans_eq
      (Finset.card_range _)
    intro p hp
    have ht := lt_of_not_ge (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ht.le))
  have hsplit : (shiftedPrimeSet x t D).card+E.card = Nat.primeCounting ⌊1+t/D⌋₊ := by
    simpa only [P, E, shiftedPrimeSet, Nat.primesLE_card_eq_primeCounting] using
      Finset.card_filter_add_card_filter_not (s := P) (fun p : ℕ => x^(9/10 : ℝ) ≤ p)
  have hsplitR := congrArg (fun n : ℕ => (n : ℝ)) hsplit
  push_cast at hsplitR
  rw [show ((shiftedPrimeSet x t D).card : ℝ)-(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ) = -(E.card : ℝ) by linarith,
    abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  have hf : (⌊x^(9/10 : ℝ)⌋₊ : ℝ) ≤ x^(9/10 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx _)
  exact (by exact_mod_cast he : (E.card : ℝ) ≤ (⌊x^(9/10 : ℝ)⌋₊ : ℝ)+1).trans (by linarith)

end TotientAsymptotic

end

end OAI
