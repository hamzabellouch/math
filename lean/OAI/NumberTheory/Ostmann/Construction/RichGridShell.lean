import OAI.NumberTheory.Ostmann.Construction.PrimeRichBlock

namespace OAI

/-! # Whole rich unit shells on one fixed grid -/

namespace Ostmann

open scoped BigOperators

theorem exists_rich_grid_shell (φ : ℝ → ℝ) (hmono : Monotone φ)
    (U A d u v : ℝ) (hA : 0 < A) (hd : 0 ≤ d) (hUu : U ≤ u)
    (hlen : 4 ≤ v - u) (hlarge : 8 * A ≤ d * (v - u))
    (hunit : ∀ a, U ≤ a → φ (a + 1) - φ a ≤ A)
    (hmass : d * (v - u) ≤ φ v - φ u) :
    ∃ n : ℕ, u ≤ U + n ∧ U + n + 1 ≤ v ∧
      d / 2 ≤ φ (U + n + 1) - φ (U + n) := by
  let j := ⌈u - U⌉₊
  let l := ⌊v - U⌋₊
  have huv : u ≤ v := by linarith
  have huj : u ≤ U + (j : ℝ) := by have := Nat.le_ceil (u - U); linarith
  have hju : U + (j : ℝ) < u + 1 := by
    have := Nat.ceil_lt_add_one (sub_nonneg.mpr hUu)
    change (j : ℝ) < u - U + 1 at this
    linarith
  have hlv : U + (l : ℝ) ≤ v := by
    have := Nat.floor_le (show 0 ≤ v - U by linarith)
    change (l : ℝ) ≤ v - U at this
    linarith
  have hvl : v < U + (l : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (v - U)
    change v - U < (l : ℝ) + 1 at this
    linarith
  have hjl : j ≤ l := by
    by_contra! hbad
    have hbad' : (l : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hbad)
    linarith
  have hleft : φ (U + j) - φ u ≤ A := by
    have h := hunit u hUu
    have hm := hmono hju.le
    linarith
  have hright : φ v - φ (U + l) ≤ A := by
    have h := hunit (U + l) (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hm := hmono hvl.le
    linarith
  have hN : ((l - j : ℕ) : ℝ) ≤ v - u := by rw [Nat.cast_sub hjl]; linarith
  by_contra! hn
  have hsmall (i : ℕ) (hi : i ∈ Finset.range (l - j)) :
      φ (U + ((j + i : ℕ) : ℝ) + 1) - φ (U + ((j + i : ℕ) : ℝ)) ≤ d / 2 := by
    have hi' := Finset.mem_range.mp hi
    have hij : (j : ℝ) ≤ (j + i : ℕ) := by exact_mod_cast (Nat.le_add_right j i)
    have hil : ((j + i : ℕ) : ℝ) + 1 ≤ l := by
      exact_mod_cast (show j + i + 1 ≤ l by omega)
    exact (hn (j + i) (by linarith) (by linarith)).le
  have hsum := Finset.sum_le_sum hsmall
  have he : (∑ i ∈ Finset.range (l - j),
      (φ (U + ((j + i : ℕ) : ℝ) + 1) - φ (U + ((j + i : ℕ) : ℝ)))) =
        φ (U + l) - φ (U + j) := by
    have ht := Finset.sum_range_sub (fun i : ℕ => φ (U + ((j + i : ℕ) : ℝ))) (l - j)
    simpa only [Nat.add_sub_of_le hjl, Nat.add_zero, Nat.cast_add,
      Nat.cast_one, ← add_assoc] using ht
  rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

/-- The upper-block selection in the character argument, including whole
rich unit shells from the single grid based at the selected left endpoint. -/
theorem exists_rich_prime_grid_block {C : ℝ} (hMertens : MertensEstimate C)
    (M : ℕ) (hM : 0 < M) (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (hmesh : 20 ≤ ε * M) :
    ∃ H : ℕ, ∀ (K : ℕ), 1 ≤ K → 4 ≤ ε * K →
      64 * (Real.exp 1 + 1) ≤ d * ε * K →
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ a L : ℝ, max C 0 ≤ a → 0 ≤ L →
      2 * (Real.exp 1 + 1) * (5 * K * (M : ℝ) ^ H + 1) < d * L →
      d * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) a (a + L) →
      ∃ (j : ℕ) (U : ℝ), j ≤ H ∧ a ≤ U ∧
        U + 5 * K * (M : ℝ) ^ j ≤ a + L ∧
        ∀ u v : ℝ, U ≤ u → v ≤ U + 5 * K * (M : ℝ) ^ j →
          ε * (K * (M : ℝ) ^ j) ≤ v - u →
          ∃ n : ℕ, u ≤ U + n ∧ U + n + 1 ≤ v ∧
            d / 16 ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹) (U + n) (U + n + 1) := by
  obtain ⟨H, hH⟩ := exists_rich_prime_subblock hMertens M hM d hd
  refine ⟨H, ?_⟩
  intro K hK hKε hKA P hP a L ha hL hlarge hroot
  obtain ⟨j, U, hj, haU, hUL, hrich⟩ := hH K hK P hP a L ha hL hlarge hroot
  refine ⟨j, U, hj, haU, hUL, ?_⟩
  intro u v hUu hv hlen
  let k := (K : ℝ) * (M : ℝ) ^ j
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hk : (K : ℝ) ≤ k := by
    dsimp [k]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hM1)
  have hkpos : 0 < k := lt_of_lt_of_le (by exact_mod_cast (show 0 < K by omega)) hk
  have hlen4 : 4 ≤ v - u := hKε.trans ((mul_le_mul_of_nonneg_left hk hε.le).trans hlen)
  have hgrid : 4 * (5 * K * (M : ℝ) ^ j / M) ≤ v - u := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have h := mul_le_mul_of_nonneg_right hmesh hkpos.le
    have hdiv : 4 * (5 * k / M) ≤ ε * k := by
      rw [show 4 * (5 * k / M) = 20 * k / M by ring]
      apply (div_le_iff₀ hMr).mpr
      nlinarith only [h]
    convert hdiv.trans hlen using 1; dsimp [k]; ring
  have hm := hrich u v hUu (by linarith) hv hgrid
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have hmass : (d / 8) * (v - u) ≤ φ v - φ u := by
    rwa [weightedCDF_sub _ _ _ u v (by linarith)]
  have hlarge' : 8 * (Real.exp 1 + 1) ≤ (d / 8) * (v - u) := by
    have h := mul_le_mul_of_nonneg_left hk (mul_nonneg hd.le hε.le)
    have h' := mul_le_mul_of_nonneg_left hlen hd.le
    nlinarith
  obtain ⟨n, hn, hnv, hnmass⟩ := exists_rich_grid_shell φ hmono U (Real.exp 1 + 1)
    (d / 8) u v (by positivity) (by positivity) hUu hlen4 hlarge'
    (by
      intro b hb
      rw [weightedCDF_sub _ _ _ b (b + 1) (by linarith)]
      exact prime_loglog_unit_mass_upper hMertens P hP b (ha.trans (haU.trans hb))) hmass
  refine ⟨n, hn, hnv, ?_⟩
  rw [weightedCDF_sub _ _ _ (U + n) (U + n + 1) (by linarith)] at hnmass
  convert hnmass using 1; ring

end Ostmann

end OAI
