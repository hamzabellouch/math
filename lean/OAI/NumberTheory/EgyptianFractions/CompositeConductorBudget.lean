import OAI.NumberTheory.EgyptianFractions.CompositeSpectral

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- A finite reciprocal-square tail with a uniform strict margin below one. -/
theorem reciprocal_square_Icc_bound (N : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤
      3 / 4 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hid : (1 : ℝ) / ((N : ℝ) * (N + 1)) = 1 / N - 1 / (N + 1) := by
      field_simp
      ring
    have hterm : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤
        1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
      rw [← hid]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith

/-- At most `d` residues have additive order `d`, including orders which do
not divide the modulus. For divisors, the exact count is Euler's totient. -/
theorem order_fiber_card_le (q d : ℕ) [NeZero q] :
    ((Finset.univ : Finset (ZMod q)).filter (fun r => addOrderOf r = d)).card ≤ d := by
  classical
  by_cases hd : d ∣ q
  · have hcount := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod q)
      (show d ∣ Fintype.card (ZMod q) by simpa using hd)
    rw [hcount]
    exact Nat.totient_le d
  · have hempty : ((Finset.univ : Finset (ZMod q)).filter
        (fun r => addOrderOf r = d)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have heq := (Finset.mem_filter.mp hr).2
      apply hd
      have horder := addOrderOf_dvd_card (x := r)
      simpa only [heq, ZMod.card] using horder
    simp [hempty]

/-- The total cubic reciprocal-conductor mass is uniformly at most `3/4`.
This controls the sixth moment when the normalized character bound at
conductor `d` is `1 / sqrt d`. -/
theorem conductor_cube_sum_le (q : ℕ) [NeZero q] :
    (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      (1 : ℝ) / (addOrderOf r : ℝ) ^ 3) ≤ 3 / 4 := by
  classical
  have hmap : ∀ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      addOrderOf r ∈ Finset.Icc 2 q := by
    intro r hr
    have hr0 := (Finset.mem_erase.mp hr).1
    have hp := addOrderOf_pos r
    have hne : addOrderOf r ≠ 1 := by
      intro h
      exact hr0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
    have hd : addOrderOf r ∣ q := by simpa using addOrderOf_dvd_card (x := r)
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_of_dvd (NeZero.pos q) hd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun r : ZMod q => (1 : ℝ) / (addOrderOf r : ℝ) ^ 3)]
  have hsum :
      (∑ d ∈ Finset.Icc 2 q,
        ∑ r ∈ (Finset.univ.erase 0).filter (fun r : ZMod q => addOrderOf r = d),
          (1 : ℝ) / (addOrderOf r : ℝ) ^ 3) ≤
      ∑ d ∈ Finset.Icc 2 q, (1 : ℝ) / (d : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have := (Finset.mem_Icc.mp hd).1; omega)
    have hcard : ((Finset.univ.erase 0).filter
        (fun r : ZMod q => addOrderOf r = d)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans
        (order_fiber_card_le q d)
    calc
      _ = (((Finset.univ.erase 0).filter
          (fun r : ZMod q => addOrderOf r = d)).card : ℝ) * (1 / (d : ℝ) ^ 3) := by
        calc
          _ = ∑ r ∈ (Finset.univ.erase 0).filter
              (fun r : ZMod q => addOrderOf r = d), (1 : ℝ) / (d : ℝ) ^ 3 := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [(Finset.mem_filter.mp hr).2]
          _ = _ := by simp
      _ ≤ (d : ℝ) * (1 / (d : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 1 / (d : ℝ) ^ 2 := by field_simp
  apply hsum.trans
  by_cases hq : 2 ≤ q
  · exact (reciprocal_square_Icc_bound q hq).trans (sub_le_self _ (by positivity))
  · have he : Finset.Icc 2 q = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    norm_num [he]

/-- Additive order is exactly the conductor obtained by cancelling the
frequency against the modulus. -/
theorem order_eq_reduced_modulus {q : ℕ} [NeZero q] (r : ZMod q) :
    addOrderOf r = q / r.val.gcd q := by
  simpa only [ZMod.natCast_zmod_val, Nat.gcd_comm] using
    ZMod.addOrderOf_coe r.val (NeZero.ne q)

/-- A pointwise inverse-square-root conductor estimate supplies six products
with every target sum. No residue-distribution hypothesis is silently assumed:
the actual character estimate is a premise of this theorem. -/
theorem six_products_of_conductor_bound {q : ℕ} [NeZero q]
    (H : Finset (ZMod q)) (hH : H.Nonempty)
    (hchar : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ a ∈ H, ∑ b ∈ H, ZMod.stdAddChar (a * b * r)‖ ≤
        (H.card : ℝ) ^ 2 / Real.sqrt (addOrderOf r : ℝ))
    (t : ZMod q) :
    ∃ a b : Fin 6 → H, ∑ i, (a i : ZMod q) * (b i : ZMod q) = t := by
  classical
  apply products_sum_of_character_bounds H 6 t
    (fun r => (H.card : ℝ) ^ 2 / Real.sqrt (addOrderOf r : ℝ)) hchar
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
  have hpower (r : ZMod q) :
      ((H.card : ℝ) ^ 2 / Real.sqrt (addOrderOf r : ℝ)) ^ 6 =
        (H.card : ℝ) ^ 12 * (1 / (addOrderOf r : ℝ) ^ 3) := by
    rw [div_pow]
    have hs : Real.sqrt (addOrderOf r : ℝ) ^ 6 = (addOrderOf r : ℝ) ^ 3 := by
      calc
        _ = (Real.sqrt (addOrderOf r : ℝ) ^ 2) ^ 3 := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hs]
    ring
  simp_rw [hpower]
  rw [← Finset.mul_sum]
  have hmass := mul_le_mul_of_nonneg_left (conductor_cube_sum_le q)
    (show 0 ≤ (H.card : ℝ) ^ 12 by positivity)
  have hstrict : (H.card : ℝ) ^ 12 * (3 / 4) < (H.card : ℝ) ^ 12 := by
    nlinarith [pow_pos hcard 12]
  simpa only [show 2 * 6 = 12 by omega] using hmass.trans_lt hstrict

end Problem337.CompositeSpectral

end

end OAI
