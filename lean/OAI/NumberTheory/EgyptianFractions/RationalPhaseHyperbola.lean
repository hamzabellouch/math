import OAI.NumberTheory.EgyptianFractions.RationalPhaseSpacing

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RationalPhaseSpacing

/-- Monotonicity in the cap, valid also at integer phases. -/
theorem truncatedInv_mono_cap {Y Z : ℝ} (hYZ : Y ≤ Z) (x : ℝ) :
    truncatedInv Y x ≤ truncatedInv Z x := by
  unfold truncatedInv
  split_ifs
  · exact hYZ
  · exact min_le_min hYZ le_rfl

/-- Positive indices in the first half-block cannot approach an integer more
closely than `1/(2q)`. This removes the artificial singular term in Type I. -/
theorem intDistance_lower_bound
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (n : ℤ) (hn : n ≠ 0) (hsmall : 2 * |n| ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ intDistance (α * n) := by
  simpa only [intDistance_eq_abs_sub_round] using
    separation_of_rational_approximation α a q hq hcop happrox n hn hsmall (round (α * n))

/-- First-block harmonic estimate with arbitrary, even varying, caps. The
bound is independent of those caps because zero frequency is excluded. -/
theorem sum_truncatedInv_first_block_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (cap : ℤ → ℝ) :
    (∑ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      truncatedInv (cap n) (intDistance (α * n))) ≤
      8 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf : (2 : ℤ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
  have hspan : ∀ m ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      ∀ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ), 2 * |m - n| ≤ (q : ℤ) := by
    intro m hm n hn
    apply short_interval_span q 0 m _ n _
    · have hh := Finset.mem_Ico.mp hm
      apply Finset.mem_Ico.mpr
      push_cast at hh ⊢
      omega
    · have hh := Finset.mem_Ico.mp hn
      apply Finset.mem_Ico.mpr
      push_cast at hh ⊢
      omega
  have hpoint : ∀ n ∈ Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ),
      truncatedInv (cap n) (intDistance (α * n)) ≤
        truncatedInv (2 * (q : ℝ)) (intDistance (α * n)) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hnp : 0 < n := by omega
    have hsmall : 2 * |n| ≤ (q : ℤ) := by
      rw [abs_of_pos hnp]
      push_cast at hn'
      omega
    have hd := intDistance_lower_bound α a q hq hcop happrox n (by omega) hsmall
    have hdp : 0 < intDistance (α * n) := (by positivity : (0 : ℝ) < 1 / (2 * q)).trans_le hd
    have hinv : 1 / intDistance (α * n) ≤ 2 * (q : ℝ) := by
      apply (div_le_iff₀ hdp).mpr
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mp hd
      nlinarith
    simp only [truncatedInv, ite_eq_right (ne_of_gt hdp), min_eq_right hinv]
    exact min_le_right _ _
  have hs := sum_truncatedInv_intDistance_le α a q hq hcop happrox
    (Finset.Ico 1 ((q / 2 + 1 : ℕ) : ℤ)) hspan (2 * (q : ℝ)) (by positivity)
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (Finset.sum_le_sum hpoint).trans (hs.trans (by nlinarith))

/-- On later blocks the hyperbolic cap `X/n` is bounded by the cap at the
left endpoint. This is the actual ingredient that removes an `O(X)` error. -/
theorem sum_truncatedInv_hyperbolic_block_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (hL : 0 < L) (X : ℝ) (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Ico L (L + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      2 * X / (L : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hs := sum_truncatedInv_intDistance_short_interval_le α a q hq hcop happrox
    L (X / (L : ℝ)) (by positivity)
  have hpoint : ∀ n ∈ Finset.Ico L (L + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n)) ≤
        truncatedInv (X / (L : ℝ)) (intDistance (α * n)) := by
    intro n hn
    apply truncatedInv_mono_cap
    apply div_le_div_of_nonneg_left hX hLr
    exact_mod_cast (Finset.mem_Ico.mp hn).1
  apply (Finset.sum_le_sum hpoint).trans
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, mul_div_assoc] using hs

/-- Prefix aggregation with hyperbolic caps. The first block has no singular
term; the remaining singular terms sum harmonically rather than linearly. -/
theorem sum_truncatedInv_hyperbolic_prefix_blocks_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (k : ℕ) :
    (∑ n ∈ Finset.Ico 1 ((k : ℤ) * (q / 2 + 1 : ℕ) + (q / 2 + 1 : ℕ)),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      ((k : ℝ) + 2) * (4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) +
        (2 * X / ((q / 2 + 1 : ℕ) : ℝ)) * (harmonic k : ℝ) := by
  let B : ℕ := q / 2 + 1
  let C : ℝ := 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))
  change (∑ n ∈ Finset.Ico 1 ((k : ℤ) * B + B),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      ((k : ℝ) + 2) * C + (2 * X / (B : ℝ)) * (harmonic k : ℝ)
  have hB : 0 < B := by dsimp [B]; omega
  have hBz : (0 : ℤ) < B := by exact_mod_cast hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  induction k with
  | zero =>
    have hs := sum_truncatedInv_first_block_le α a q hq hcop happrox (fun n => X / (n : ℝ))
    convert hs using 1 <;> simp [B, C]
    ring
  | succ k ih =>
    have hmiddle : 0 < (k : ℤ) * B + B := by positivity
    have hleft : (1 : ℤ) ≤ (k : ℤ) * B + B := by omega
    have hright : (k : ℤ) * B + B ≤ (k : ℤ) * B + B + B := by omega
    have hend : ((k + 1 : ℕ) : ℤ) * B + B = (k : ℤ) * B + B + B := by
      push_cast
      ring
    rw [hend, ← sum_int_Ico_add _ 1 ((k : ℤ) * B + B)
      ((k : ℤ) * B + B + B) hleft hright]
    have hblock := sum_truncatedInv_hyperbolic_block_le α a q hq hcop happrox
      ((k : ℤ) * B + B) hmiddle X hX
    have hrecip : 2 * X / ((k : ℝ) * B + B) =
        (2 * X / (B : ℝ)) * (1 / ((k : ℝ) + 1)) := by
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hfactor : (k : ℝ) * B + B = (B : ℝ) * ((k : ℝ) + 1) := by ring
      rw [hfactor]
      field_simp
    have hblock' : (∑ n ∈ Finset.Ico ((k : ℤ) * B + B) ((k : ℤ) * B + B + B),
        truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
        (2 * X / (B : ℝ)) * (1 / ((k : ℝ) + 1)) + C := by
      change (∑ n ∈ Finset.Ico ((k : ℤ) * B + B) ((k : ℤ) * B + B + B),
          truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
          2 * X / (((k : ℤ) * B + B : ℤ) : ℝ) + C at hblock
      push_cast at hblock
      simpa only [hrecip] using hblock
    have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
      rw [harmonic_succ]
      push_cast
      simp only [one_div]
    apply (add_le_add ih hblock').trans
    rw [hharm]
    push_cast
    ring_nf
    exact le_rfl

/-- A uniform hyperbolic reciprocal-distance bound. This is the scalar
Type-I estimate: the potentially large cap contributes `X/q`, not `X`. -/
theorem sum_truncatedInv_hyperbolic_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 (M : ℤ),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
      8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) +
        (4 * X / (q : ℝ)) * (1 + Real.log ((M : ℝ) + 1)) := by
  let B : ℕ := q / 2 + 1
  let k : ℕ := M / B
  let C : ℝ := 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))
  have hB : 0 < B := by dsimp [B]; omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcover : (M : ℤ) < (k : ℤ) * B + B := by
    exact_mod_cast (Nat.lt_div_mul_add (a := M) hB)
  have hsub : Finset.Icc 1 (M : ℤ) ⊆ Finset.Ico 1 ((k : ℤ) * B + B) := by
    intro n hn
    have hh := Finset.mem_Icc.mp hn
    exact Finset.mem_Ico.mpr ⟨hh.1, hh.2.trans_lt hcover⟩
  have hsum := sum_truncatedInv_hyperbolic_prefix_blocks_le α a q hq hcop happrox X hX k
  have hsum' : (∑ n ∈ Finset.Icc 1 (M : ℤ),
      truncatedInv (X / (n : ℝ)) (intDistance (α * n))) ≤
        ((k : ℝ) + 2) * C + (2 * X / (B : ℝ)) * (harmonic k : ℝ) := by
    apply le_trans ?_ hsum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    apply truncatedInv_nonneg
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ico.mp hn).1
      positivity
    · exact intDistance_nonneg _
  have hqB : (q : ℝ) ≤ 2 * (B : ℝ) := by
    exact_mod_cast (show q ≤ 2 * B by dsimp [B]; omega)
  have hkB : (k : ℝ) * B ≤ M := by exact_mod_cast Nat.div_mul_le_self M B
  have hkq : (k : ℝ) * q ≤ 2 * (M : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hqB (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hlogq : 0 ≤ 1 + Real.log (2 * (q : ℝ)) := by
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hh := Real.log_nonneg (show 1 ≤ 2 * (q : ℝ) by linarith)
    linarith
  have hCbound : ((k : ℝ) + 2) * C ≤
      8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_right hkq hlogq
    dsimp [C]
    nlinarith
  have hA : 2 * X / (B : ℝ) ≤ 4 * X / (q : ℝ) := by
    apply (div_le_div_iff₀ hBr hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hqB hX]
  have hharm : (harmonic k : ℝ) ≤ 1 + Real.log ((M : ℝ) + 1) := by
    have hkle : k ≤ M + 1 := (Nat.div_le_self M B).trans (by omega)
    have hmono : (harmonic k : ℝ) ≤ (harmonic (M + 1) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkle)
      intro n _ _
      positivity
    exact hmono.trans (by simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (M + 1))
  have hharm0 : (0 : ℝ) ≤ harmonic k := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  exact hsum'.trans (add_le_add hCbound (mul_le_mul hA hharm hharm0 (by positivity)))

end Problem337.RationalPhaseSpacing

end

end OAI
