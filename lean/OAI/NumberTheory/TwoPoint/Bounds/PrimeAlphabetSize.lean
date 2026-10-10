import OAI.NumberTheory.TwoPoint.Bounds.PrimeBlockDimension

namespace OAI

/-! The full forced-step alphabet includes all bounded padding divisors.
Its size still fits the polynomial exponential budget of finite-law
comparison; no eligibility restriction is needed for this count. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma boundedPaddingDivisor_real_upper (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L)
    (q : ℕ) (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (q : ℝ) ≤ Real.exp (100 * L ^ 2) := by
  have hr := (mem_filter.mp hq).1
  have hsq := retainedPrimeDivisor_squarefree (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hpool := retainedPrimeDivisor_factors (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) hr
  have hdeg : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L :=
    (show (q.primeFactors.card : ℝ) ≤ (⌊100 * Real.log L⌋₊ : ℝ) by
      exact_mod_cast (mem_filter.mp hq).2).trans
        (Nat.floor_le (mul_nonneg (by norm_num) (Real.log_nonneg hL)))
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc
    _ = ∏ p ∈ q.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    _ ≤ ∏ _p ∈ q.primeFactors, Real.exp L :=
      prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
        (fun p hp => paddingPrimeSupply_bounds E L (hpool hp))
    _ = Real.exp ((q.primeFactors.card : ℝ) * L) := by
      rw [prod_const, Real.exp_nat_mul]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith

lemma boundedPaddingDivisors_card (E : Finset ℕ) (L : ℝ) (hL : 1 ≤ L) :
    ((boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊).card : ℝ) ≤
      Real.exp (100 * L ^ 2) := by
  let Q := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
  let N := ⌊Real.exp (100 * L ^ 2)⌋₊
  have hp (q : Q) : 0 < q.val := retainedPrimeDivisor_pos (paddingPrimeSupply E L)
    (fun _ hp => paddingPrimeSupply_prime hp) (mem_filter.mp q.property).1
  have hq (q : Q) : q.val ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mpr (boundedPaddingDivisor_real_upper E L hL _ q.property)
  let f : Q → Fin N := fun q => ⟨q.val - 1, by have := hp q; have := hq q; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have he : a.val - 1 = b.val - 1 := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    omega
  have hc : Q.card ≤ N := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
  exact (show (Q.card : ℝ) ≤ N by exact_mod_cast hc).trans (Nat.floor_le (Real.exp_pos _).le)

lemma actual_prime_alphabet_size (E : Finset ℕ) (W L : ℝ) (hW : 1 ≤ W) (hL : 4800 ≤ L) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    let Q := boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊
    (Fintype.card (((j : Fin J) → P j) × (Q × Bool)) : ℝ) ≤ Real.exp (L ^ 4) := by
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  have hend : primeSupplyEndpoint A W J ≤ L := primeSupplyScale_endpoint W L (by linarith) (by linarith)
  have hd : Fintype.card ((j : Fin J) → P j) ≤ ⌊Real.exp (2 * L)⌋₊ := by
    apply primeTuple_card_le P (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA.le (by linarith))
    intro d
    exact centeredPrimeTuple_upper E A W L J hA hW hend (mem_image.mpr ⟨d, mem_univ _, rfl⟩)
  have hd' : (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ Real.exp (2 * L) :=
    (show (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) by exact_mod_cast hd).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hq := boundedPaddingDivisors_card E L (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ Real.exp (2 * L) * (Real.exp (100 * L ^ 2) * Real.exp L) := by gcongr
    _ = Real.exp (100 * L ^ 2 + 3 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hL2 : 103 ≤ L ^ 2 := by nlinarith
      nlinarith [mul_nonneg (show 0 ≤ L ^ 2 - 103 by linarith) (sq_nonneg L)]

end TwoPointCorrelations

end OAI
