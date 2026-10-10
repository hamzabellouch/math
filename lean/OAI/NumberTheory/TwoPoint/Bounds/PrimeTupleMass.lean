import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal
import OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyScale
import OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic

namespace OAI

/-! The centered divisor family is the actual image of one prime choice
from each disjoint band. Its harmonic mass has no representation
multiplicity and is exactly the product of the band masses. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def primeTupleDivisors {J : ℕ} (P : Fin J → Finset ℕ) : Finset ℕ :=
  univ.image (fun x : (j : Fin J) → P j => ∏ j, (x j).val)

lemma primeTupleDivisors_mass {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, ∑ p ∈ P j, 1 / (p : ℝ) := by
  rw [primeTupleDivisors, sum_image]
  · calc
      _ = ∑ x : (j : Fin J) → P j, ∏ j, 1 / ((x j).val : ℝ) := by
        apply sum_congr rfl
        intro x _
        simp only [Nat.cast_prod, one_div, prod_inv_distrib]
      _ = ∏ j, ∑ p : P j, 1 / (p.val : ℝ) :=
        (Fintype.prod_sum (fun j (p : P j) => 1 / (p.val : ℝ))).symm
      _ = _ := by
        apply prod_congr rfl
        intro j _
        exact sum_coe_sort (P j) (fun p : ℕ => 1 / (p : ℝ))
  · intro x _ y _ hxy
    exact primeTuple_injective hprime hdisjoint hxy

lemma centeredPrimeTuple_log_bound {E : Finset ℕ} {A W L : ℝ}
    (hA : 0 < A) (hW : 1 ≤ W) {J : ℕ} (hL : primeSupplyEndpoint A W J ≤ L)
    {d : ℕ} (hd : d ∈ primeTupleDivisors (fun j : Fin J => centeredPrimeSupply E A W j)) :
    0 < d ∧ Real.log d ≤ 2 * L := by
  obtain ⟨x, _, rfl⟩ := mem_image.mp hd
  constructor
  · exact prod_pos fun j _ => (centeredPrimeSupply_mem (x j).property).1.pos
  · exact (centeredPrimeSupply_tuple_log_bound hA hW hL
      (fun j => (x j).val) (fun j => (x j).property)).le

lemma centeredPrimeTuple_mass (E : Finset ℕ) (A W : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hW : 0 ≤ W) :
    (∑ d ∈ primeTupleDivisors (fun j : Fin J => centeredPrimeSupply E A W j),
      1 / (d : ℝ)) =
      ∏ j : Fin J, ∑ p ∈ centeredPrimeSupply E A W j, 1 / (p : ℝ) := by
  apply primeTupleDivisors_mass
  · intro j p hp
    exact (centeredPrimeSupply_mem hp).1
  · intro j l hne
    exact centeredPrimeSupply_pairwise_disjoint E A W hA hW
      (fun he => hne (Fin.ext he.symm))

lemma primeTupleDivisors_mass_bounds {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (W : ℝ) (hW : 0 ≤ W)
    (hmass : ∀ j, W ≤ (∑ p ∈ P j, 1 / (p : ℝ)) ∧
      (∑ p ∈ P j, 1 / (p : ℝ)) ≤ 2 * W) :
    W ^ J ≤ (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) ∧
      (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) ≤ (2 * W) ^ J := by
  rw [primeTupleDivisors_mass P hprime hdisjoint]
  constructor
  · calc
      _ = ∏ _j : Fin J, W := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => hW) (fun j _ => (hmass j).1)
  · calc
      _ ≤ ∏ _j : Fin J, 2 * W := prod_le_prod₀
        (fun j _ => sum_nonneg (fun p _ => by positivity)) (fun j _ => (hmass j).2)
      _ = _ := by simp

/-- `q:bin-mass` for the actual prime families and the manuscript's scale
choice. The assertion is uniform over the positive bin width. -/
theorem ModFiveThetaInput.eventually_primeTuple_bin_mass (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ η : ℝ, 0 < η →
      let J := primeSupplyCount W L
      let P := fun j : Fin J => centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W j
      let V := ∏ j : Fin J, ∑ p ∈ P j, 1 / (p : ℝ)
      (1 / 2 : ℝ) * paddingTiltNormalizer (paddingPrimeSupply E L) * V ≤
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ∧
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
          paddingTiltNormalizer (paddingPrimeSupply E L) * V := by
  filter_upwards [hP.eventually_totalPaddingBinMass E, eventually_ge_atTop (1 : ℝ)]
    with L hmass hL
  intro η hη
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hA : 0 < L ^ (199 / 200 : ℝ) := Real.rpow_pos_of_pos hLp _
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have he := primeSupplyScale_endpoint W L hWp hL
  have hd := hmass (primeTupleDivisors
    (fun j : Fin (primeSupplyCount W L) => centeredPrimeSupply E (L ^ (199 / 200 : ℝ)) W j))
    η hη (fun d hd => centeredPrimeTuple_log_bound hA hW he hd)
  dsimp only
  rw [centeredPrimeTuple_mass E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)
    hA.le hWp.le] at hd
  exact hd

end TwoPointCorrelations

end OAI
