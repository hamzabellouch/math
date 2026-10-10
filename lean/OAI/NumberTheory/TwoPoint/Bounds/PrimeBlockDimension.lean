import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale

namespace OAI

/-! The actual tuple copies and the length-exp(103L) block fit the
exp(106L) starting-vertex allowance in the matrix trace. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma primeTuple_card_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (Dmax : ℕ)
    (hmax : ∀ d : (j : Fin J) → P j, (∏ j, (d j).val) ≤ Dmax) :
    Fintype.card ((j : Fin J) → P j) ≤ Dmax := by
  have hp (d : (j : Fin J) → P j) : 0 < ∏ j, (d j).val :=
    prod_pos (fun j _ => (hprime j _ (d j).property).pos)
  let f : ((j : Fin J) → P j) → Fin Dmax := fun d =>
    ⟨(∏ j, (d j).val) - 1, by have := hmax d; have := hp d; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply primeTuple_injective hprime hdisjoint
    have he := congrArg Fin.val hab
    have ha := hp a
    have hb := hp b
    change (∏ j, (a j).val) - 1 = (∏ j, (b j).val) - 1 at he
    change (∏ j, (a j).val) = (∏ j, (b j).val)
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem actual_prime_block_dimension (E : Finset ℕ) (W L : ℝ)
    (hW : 1 ≤ W) (hL : 1 ≤ L) :
    let J := primeSupplyCount W L
    let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
    (Fintype.card (((j : Fin J) → P j) × Fin ⌈Real.exp (103 * L)⌉₊) : ℝ) ≤
      Real.exp (106 * L) := by
  dsimp only
  let J := primeSupplyCount W L
  let A := L ^ (199 / 200 : ℝ)
  let P := centeredPrimeBands E A W J
  have hA : 0 < A := Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
  have hend : primeSupplyEndpoint A W J ≤ L :=
    primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL
  have hd : Fintype.card ((j : Fin J) → P j) ≤ ⌊Real.exp (2 * L)⌋₊ := by
    apply primeTuple_card_le P (centeredPrimeBands_prime E A W J)
      (centeredPrimeBands_disjoint E A W J hA.le (zero_le_one.trans hW))
    intro d
    exact centeredPrimeTuple_upper E A W L J hA hW hend (mem_image.mpr ⟨d, mem_univ _, rfl⟩)
  have hdc : (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ (⌊Real.exp (2 * L)⌋₊ : ℝ) := by
    exact_mod_cast hd
  have hd' : (Fintype.card ((j : Fin J) → P j) : ℝ) ≤ Real.exp (2 * L) :=
    hdc.trans (Nat.floor_le (Real.exp_pos _).le)
  have hm : (⌈Real.exp (103 * L)⌉₊ : ℝ) ≤ 2 * Real.exp (103 * L) := by
    have he := Real.one_le_exp (show 0 ≤ 103 * L by linarith)
    have hc : (⌈Real.exp (103 * L)⌉₊ : ℝ) ≤ Real.exp (103 * L) + 1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ Real.exp (103 * L) from (Real.exp_pos _).le)).le
    linarith
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  calc
    _ ≤ Real.exp (2 * L) * (2 * Real.exp (103 * L)) :=
      mul_le_mul hd' hm (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = 2 * (Real.exp (2 * L) * Real.exp (103 * L)) := by ring
    _ = 2 * Real.exp (105 * L) := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp L * Real.exp (105 * L) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp L]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI
