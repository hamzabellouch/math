import OAI.NumberTheory.TwoPoint.Bounds.RareRowDecay

namespace OAI

/-! The row-moment and rare-site bounds for the literal centered prime
bands. All mass and scale assumptions are supplied by the fixed-modulus
prime theorem and the actual band-count definition. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma primeRowMajorant_nonneg {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ) (n : ℤ) :
    0 ≤ primeRowMajorant P Q n := by
  apply mul_nonneg (zero_le_one.trans (actualPaddingWeight_one_le Q n))
  apply prod_nonneg
  intro j _
  apply add_nonneg (Nat.cast_nonneg _)
  unfold primeHarmonicMass
  positivity

theorem ModFiveThetaInput.eventually_actual_row_second_moment (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 10 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ),
      (data.residueLaw B hB).average (fun x =>
        (primeRowMajorant (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L))
          data.Q (data.residueOrigin x + site)) ^ 2) ≤ L ^ (25 : ℕ) := by
  filter_upwards [hP.eventually_actual_prime_supplies E W (by linarith),
    hP.eventually_padding_pool_mass E, eventually_ge_atTop (1 : ℝ)] with L hs hq hL
  intro h M B data hp hqeq hB site
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hA : 0 ≤ A := Real.rpow_nonneg (by linarith) _
  have hsub (j : Fin J) : P j ⊆ data.P := by
    rw [hp]
    exact centeredPrimeBand_subset_pool E A W J j
  have hdisjoint (j l : Fin J) (hne : l ≠ j) : Disjoint (P j) (P l) :=
    centeredPrimeBands_disjoint E A W J hA (by linarith) j l hne
  have hV (j : Fin J) : primeHarmonicMass (P j) ≤ 2 * W := by
    simpa only [P, centeredPrimeBands, primeHarmonicMass_eq_sum, A] using (hs.2.2 j.val).2.2
  have hQ : (∑ p ∈ data.Q, 1 / (p : ℝ)) ≤ Real.log L := by
    rw [hqeq, ← primeHarmonicMass_eq_sum]
    exact hq
  have hJ : (J : ℝ) * (6 * W) ≤ Real.log L := by
    have hj := primeSupplyCount_mul_bound W L (by linarith) hL
    have hl := Real.log_nonneg hL
    change (J : ℝ) * (6 * W) ≤ (1 / 200 : ℝ) * Real.log L at hj
    linarith
  exact data.prime_row_second_moment_polynomial hB P hsub hdisjoint site L W hL hW hQ hV hJ

theorem ModFiveThetaInput.eventually_actual_rare_row (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
        (bad : (↥(data.P ∪ data.Q) → Fin B) → Prop),
      (data.residueLaw B hB).probability bad ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      ∀ A : ℝ, 0 ≤ A → A ≤ Real.exp (C * Real.log L) →
      A * (data.residueLaw B hB).average (fun x =>
        primeRowMajorant (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L))
          data.Q (data.residueOrigin x + site) * if bad x then 1 else 0) ≤
            Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [hP.eventually_actual_row_second_moment E W hW,
    eventually_rare_row_decay C hC, eventually_ge_atTop (1 : ℝ)] with L hm hd hL
  intro h M B data hp hq hB site bad hbad A hA hAcap
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
  let F := fun x : ↥(data.P ∪ data.Q) → Fin B =>
    primeRowMajorant P data.Q (data.residueOrigin x + site)
  have hF : ∀ x, 0 ≤ F x := fun x => primeRowMajorant_nonneg P data.Q _
  have hs := (data.residueLaw B hB).square_event_average_le F bad
  have hL0 : 0 ≤ L := by linarith
  have hmoment : (data.residueLaw B hB).average (fun x => (F x) ^ 2) ≤ L ^ (25 : ℕ) :=
    hm h M B data hp hq hB site
  have hsq := hs.trans (mul_le_mul hmoment hbad
    ((data.residueLaw B hB).probability_nonneg bad) (by positivity))
  exact hd A _ hA ((data.residueLaw B hB).average_nonneg (fun x =>
    mul_nonneg (hF x) (by split_ifs <;> norm_num))) hAcap hsq

end TwoPointCorrelations

end OAI
