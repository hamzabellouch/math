import OAI.NumberTheory.JointDickman.Arithmetic.PrimeChannelMarginal

namespace OAI

/-! # The actual residue-channel estimate from published analytic inputs

No marginal, conditional-cell, or high-exclusive approximation is assumed
here: all three are derived from the cited input estimates.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def residueChannelError (M C T : ℝ) (B : ℕ) (m mass : ℝ) : ℝ :=
  8 * (T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) *
      (M + (C * (B : ℝ) ^ (-(80 : ℝ)) + 9 / (8 * (auxiliaryCutoff B : ℝ))) / m) +
    4 * ((2 * (C * (B : ℝ) ^ (-(80 : ℝ))) + (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 +
      9 / (8 * (auxiliaryCutoff B : ℝ))) / (m * m)) * mass

open Classical in
/-- The bound is uniform in the number of cells, their endpoints, the
modulus and the real input. It uses only structural conditions on the cells. -/
theorem primeResidueChannel_from_published
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C T : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < T ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (D : Type*) [Fintype D] [DecidableEq D],
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ lower upper : D → ℝ,
      (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
      (∀ d, 1 / 2 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
      ∀ δ : ℝ, 0 < δ → (∀ d, upper d - lower d = δ) →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      let m := δ / (q.totient : ℝ)
      let U := finiteChannel (fullPrimeMass (auxiliaryPrimes B)) (fun _ => m)
        (partialFairPrimeTransition (auxiliaryPrimes B) (logResidueCell B q lower upper)) f
      (∑ a : D × (ZMod q)ˣ, m * (U a - finiteResidueAverage (fun r => U (a.1, r))) ^ 2) ≤
        residueChannelError M C T B m (∑ _a : D × (ZMod q)ˣ, m) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨v, _, _, H, C₀, hC₀, hhigh⟩ := highExclusiveLogCell_local_law hSD hSW hM
  obtain ⟨M₁, C₁, hM₁, hC₁, hcommon⟩ := primeCommonLogCell_upper hSD hSW hM hMP
  obtain ⟨M₂, C₂, hM₂, hC₂, hmarginal⟩ := primeChannelMarginal_upper hSD hSW hM hMP
  obtain ⟨T, hT, htail⟩ := quarterPrimeMass_small_log_tail hM
  let M := M₁ + M₂
  let C := C₀ + C₁ + C₂
  have hM0 : 0 ≤ M := add_nonneg hM₁ hM₂
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 4 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
    exact (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
      (fun _ h => h.le)
  refine ⟨M, C, T, hM0, hC, hT, ?_⟩
  filter_upwards [hhigh, hcommon, hmarginal, htail, hsmall, eventually_ge_atTop 2]
    with B hhighB hcommonB hmarginalB htailB hsmallB hB
  intro D _ _ q _ hq lower upper hdisjoint hlower horder hupper δ hδ hwidth f
  let m := δ / (q.totient : ℝ)
  let E := C * (B : ℝ) ^ (-(80 : ℝ))
  let κ := 9 / (8 * (auxiliaryCutoff B : ℝ))
  let A := M + (E + κ) / m
  let low := lowPrimeLog (auxiliaryPrimes B) B ((B : ℝ) ^ (-(1 / 10 : ℝ)))
  let profile (c : auxiliaryPrimes B → Bool) (d : D) :=
    clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
      ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d) (upper d)
      (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hm : 0 < m := div_pos hδ hφ
  have hE : 0 ≤ E := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg B) _)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hA : 0 ≤ A := add_nonneg hM0 (div_nonneg (add_nonneg hE hκ) hm.le)
  have hAM : A * m = M * m + E + κ := by dsimp [A]; field_simp; ring
  have hN : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have hcut : ∀ p ∈ auxiliaryPrimes B, auxiliaryCutoff B < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have hmar : ∀ a : D × (ZMod q)ˣ,
      independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B))
        (quarterPrimeMass (auxiliaryPrimes B))
        (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) a ≤ A * m := by
    rintro ⟨d, r⟩
    have hb := hmarginalB D q hq lower upper hdisjoint (fun d => by linarith [hlower d])
      horder hupper d r
    rw [hwidth d] at hb
    have hMC : M₂ * δ / (q.totient : ℝ) ≤ M * m := by
      have hle : M₂ ≤ M := by dsimp [M]; linarith
      simpa only [m, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hle (div_nonneg hδ.le hφ.le)
    have hEC : C₂ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      dsimp [C]
      linarith
    rw [hAM]
    linarith
  have hcom : ∀ e, low e → ∀ a : D × (ZMod q)ˣ,
      optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
        (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c e) a ≤ A * m := by
    intro e he
    rintro ⟨d, r⟩
    have he' : lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e := le_trans he hsmallB
    have hb := hcommonB D q hq lower upper hdisjoint hlower horder hupper e he' d r
    rw [hwidth d] at hb
    have hMC : M₁ * δ / (q.totient : ℝ) ≤ M * m := by
      have hle : M₁ ≤ M := by dsimp [M]; linarith
      simpa only [m, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hle (div_nonneg hδ.le hφ.le)
    have hEC : C₁ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      dsimp [C]
      linarith
    rw [hAM]
    linarith
  have hloc : ∀ c d r,
      |highExclusiveCell (quarterPrimeMass (auxiliaryPrimes B))
          (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) low c (d, r) -
        profile c d| ≤ E := by
    intro c d r
    refine (hhighB D q hq lower upper hdisjoint hupper c d r).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    dsimp [C]
    linarith
  have hout := partialFairPrimeResidueChannel_square_bound (auxiliaryPrimes B)
    (auxiliaryPrimes_prime B) hN hcut (logResidueCell B q lower upper) low profile hm hA hE
    hmar hcom hloc f
  have hσ : lowExclusiveProbability (quarterPrimeMass (auxiliaryPrimes B)) low ≤
      T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) :=
    htailB _ (Real.rpow_nonneg (Nat.cast_nonneg B) _) (hsmallB.trans (by norm_num))
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  refine hout.trans (mul_le_mul_of_nonneg_right ?_ hin)
  change 8 * lowExclusiveProbability (quarterPrimeMass (auxiliaryPrimes B)) low * A + _ ≤ _
  dsimp only [residueChannelError]
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 8)) hA) le_rfl

end JointDickman

end OAI
