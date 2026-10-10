import OAI.NumberTheory.TwoPoint.Bounds.ActualRareRow
import OAI.NumberTheory.TwoPoint.Bounds.PositiveRowMajorant

namespace OAI

/-! Sum the rare-site estimate over the polynomially many bins. The
row bound is applied in the product model before integer transfer. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma positive_rare_row_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q D : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors Q)
    (n : ℤ) (bad : Prop) :
    (∑ d ∈ D, ∑ q ∈ padding d,
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        if (q : ℤ) ∣ n ∧ bad then 1 else 0) ≤
      primeRowMajorant P Q n * if bad then 1 else 0 := by
  by_cases hb : bad
  · simp only [hb, and_true, ite_true, mul_one]
    exact positive_tuple_padding_row_bound P hprime hdisjoint Q D hQ hD padding hpadding n
  · simp only [hb, and_false, ite_false, mul_zero, sum_const_zero, le_refl]

theorem ModFiveThetaInput.eventually_actual_rare_row_sum (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ) (bins : Finset ℤ),
      (bins.card : ℝ) ≤ Real.exp (C * Real.log L) →
      ∀ (bad : ℤ → (↥(data.P ∪ data.Q) → Fin B) → Prop),
      (∀ j ∈ bins, (data.residueLaw B hB).probability (bad j) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ))) →
      (∑ j ∈ bins, (data.residueLaw B hB).average (fun x =>
        primeRowMajorant (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L))
          data.Q (data.residueOrigin x + site) * if bad j x then 1 else 0)) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) := by
  filter_upwards [hP.eventually_actual_rare_row E W C hW hC] with L hb
  intro h M B data hp hq hB site bins hbins bad hbad
  by_cases hempty : bins = ∅
  · subst bins
    simp only [sum_empty]
    exact (Real.exp_pos _).le
  have hcard : 0 < (bins.card : ℝ) := by
    exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hempty)
  have hs : (bins.card : ℝ) *
      (∑ j ∈ bins, (data.residueLaw B hB).average (fun x =>
        primeRowMajorant (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L))
          data.Q (data.residueOrigin x + site) * if bad j x then 1 else 0)) ≤
      (bins.card : ℝ) * Real.exp (-L ^ (9 / 10 : ℝ)) := by
    rw [mul_sum]
    calc
      _ ≤ ∑ _j ∈ bins, Real.exp (-L ^ (9 / 10 : ℝ)) := by
        apply sum_le_sum
        intro j hj
        exact hb h M B data hp hq hB site (bad j) (hbad j hj) bins.card hcard.le hbins
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  exact le_of_mul_le_mul_left hs hcard

end TwoPointCorrelations

end OAI
