import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.RectangleNumerics

noncomputable def quarterWidth (H N : ℝ) (j : Fin 3) : ℝ :=
  8 * H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)

noncomputable def width (H N : ℝ) (j : Fin 3) : ℝ :=
  32 * H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)

noncomputable def truncation (H N : ℝ) (j : Fin 3) : ℕ :=
  ⌊width H N j / 4⌋₊

theorem width_div_four (H N : ℝ) (j : Fin 3) :
    width H N j / 4 = quarterWidth H N j := by
  unfold width quarterWidth
  ring

theorem quarterWidth_lt_truncation_add_one (H N : ℝ) (j : Fin 3) :
    quarterWidth H N j < (truncation H N j : ℝ) + 1 := by
  simpa only [truncation, width_div_four] using
    (Nat.lt_floor_add_one (quarterWidth H N j))

theorem truncation_eq_integer_floor (H N : ℝ) (hH : 0 < H) (hN : 0 < N)
    (j : Fin 3) : (truncation H N j : ℤ) = ⌊width H N j / 4⌋ := by
  apply Int.natCast_floor_eq_floor
  unfold width
  positivity

theorem four_mul_truncation_le_width (H N : ℝ) (hH : 0 < H) (hN : 0 < N)
    (j : Fin 3) : 4 * (truncation H N j : ℝ) ≤ width H N j := by
  have hf : (truncation H N j : ℝ) ≤ width H N j / 4 := by
    apply Nat.floor_le
    unfold width
    positivity
  linarith

theorem narrow_scale_ge (H N : ℝ) (hH : 0 < H) (hHN : H ≤ N) :
    N ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hN : 0 < N := hH.trans_le hHN
  have hm := Real.rpow_le_rpow_of_nonpos hH hHN (by norm_num : (-1 / 3 : ℝ) ≤ 0)
  have he : N ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hN]
    norm_num
  calc
    N = N ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := he.symm
    _ ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hN.le _)

theorem quarterWidth_ge_eight_N (H N : ℝ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (j : Fin 3) : 8 * N ≤ quarterWidth H N j := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hNp : 0 < N := hHp.trans_le hHN
  have hs := narrow_scale_ge H N hHp hHN
  have he : H ^ (-1 / 3 : ℝ) ≤
      H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hH
    split_ifs <;> norm_num
  have hm := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hNp.le (4 / 3 : ℝ))
  unfold quarterWidth
  nlinarith

theorem selected_product_gt (H N : ℝ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (I : Finset (Fin 3)) (hI : I.Nonempty) :
    (4 * N) ^ I.card < ∏ j ∈ I, ((truncation H N j : ℝ) + 1) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one (hH.trans hHN)
  have hpow : (4 * N) ^ I.card < (8 * N) ^ I.card :=
    pow_lt_pow_left₀ (by linarith) (by positivity) (Finset.card_ne_zero.mpr hI)
  have hp : (8 * N) ^ I.card < ∏ j ∈ I, ((truncation H N j : ℝ) + 1) := by
    rw [← Finset.prod_const]
    exact Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => by positivity)
      (fun j _ => (quarterWidth_ge_eight_N H N hH hHN j).trans_lt
        (quarterWidth_lt_truncation_add_one H N j)) hI
  exact hpow.trans hp

theorem quarterWidth_product (H N : ℝ) (hH : 0 < H) (hN : 0 < N) :
    (∏ j : Fin 3, quarterWidth H N j) = 8 ^ 3 * N ^ 4 := by
  have heH : H ^ (2 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hH, ← Real.rpow_add hH]
    norm_num
  have heN : N ^ (4 / 3 : ℝ) * N ^ (4 / 3 : ℝ) * N ^ (4 / 3 : ℝ) = N ^ 4 := by
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    norm_num
  rw [Fin.prod_univ_three]
  change (8 * H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ)) *
      (8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ)) *
      (8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ)) = _
  calc
    _ = 8 ^ 3 * (H ^ (2 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) * H ^ (-1 / 3 : ℝ)) *
        (N ^ (4 / 3 : ℝ) * N ^ (4 / 3 : ℝ) * N ^ (4 / 3 : ℝ)) := by ring
    _ = _ := by rw [heH, heN]; ring

theorem full_product_gt (H N : ℝ) (hH : 0 < H) (hN : 0 < N) :
    (4 * N) ^ 4 < ∏ j : Fin 3, ((truncation H N j : ℝ) + 1) := by
  have hp : (∏ j : Fin 3, quarterWidth H N j) <
      ∏ j : Fin 3, ((truncation H N j : ℝ) + 1) := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro j _
      unfold quarterWidth
      positivity
    · intro j _
      exact quarterWidth_lt_truncation_add_one H N j
    · exact Finset.univ_nonempty
  rw [quarterWidth_product H N hH hN] at hp
  have hn4 : 0 < N ^ 4 := pow_pos hN _
  have : (4 * N) ^ 4 < (8 : ℝ) ^ 3 * N ^ 4 := by nlinarith
  exact this.trans hp

theorem length_bounds_incompatible (H N : ℝ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (h : ℕ) (hh : 1 ≤ h) (hh4 : h ≤ 4) (I : Finset (Fin 3))
    (hcard : I.card = min h 3) (L : ℝ)
    (upper : L ≤ (4 * N) ^ h)
    (lower : (∏ j ∈ I, ((truncation H N j : ℝ) + 1)) ≤ L) : False := by
  by_cases hh3 : h ≤ 3
  · have hic : I.card = h := by simpa [min_eq_left hh3] using hcard
    have hi : I.Nonempty := Finset.card_pos.mp (by omega)
    have hc := selected_product_gt H N hH hHN I hi
    rw [hic] at hc
    exact (not_lt_of_ge (lower.trans upper)) hc
  · have he : h = 4 := by omega
    have hi : I = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa [he] using hcard.ge
    have hc := full_product_gt H N (by linarith) (by linarith)
    rw [he] at upper
    rw [hi] at lower
    exact (not_lt_of_ge (lower.trans upper)) hc

theorem length_bounds_incompatible_nat (H N h : ℕ) (hH : 0 < H) (hHN : H ≤ N)
    (hh : 1 ≤ h) (hh4 : h ≤ 4) (I : Finset (Fin 3))
    (hcard : I.card = min h 3) (L : ℝ)
    (upper : L ≤ (4 * (N : ℝ)) ^ h)
    (lower : (∏ j ∈ I, ((truncation H N j : ℝ) + 1)) ≤ L) : False := by
  exact length_bounds_incompatible H N (by exact_mod_cast hH) (by exact_mod_cast hHN)
    h hh hh4 I hcard L upper lower

end WeightedTorusJets.RectangleNumerics

end

end SiegelZeros

end OAI
