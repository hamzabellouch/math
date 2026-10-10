import OAI.Geometry.PeriodicTiling.WordRule
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

universe uK uα

namespace PeriodicTilingThree

attribute [local instance] Classical.propDecidable

section Field

variable {K : Type uK} [Field K]

theorem affine_coefficients_eq_of_two {a b c d x y : K} (hxy : x ≠ y)
    (hx : a * x + b = c * x + d) (hy : a * y + b = c * y + d) :
    a = c ∧ b = d := by
  have hm : (a - c) * (x - y) = 0 := by linear_combination hx - hy
  have ha : a = c := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right
    (sub_ne_zero.mpr hxy))
  refine ⟨ha, ?_⟩
  linear_combination hx - x * ha

theorem affine_root_unique {a b x y : K} (hab : a ≠ 0 ∨ b ≠ 0)
    (hx : a * x + b = 0) (hy : a * y + b = 0) : x = y := by
  by_contra hxy
  have h := affine_coefficients_eq_of_two hxy
    (show a * x + b = 0 * x + 0 by simpa using hx)
    (show a * y + b = 0 * y + 0 by simpa using hy)
  exact hab.elim (fun ha => ha h.1) (fun hb => hb h.2)

theorem affine_roots_card_le_one {α : Type uα} [DecidableEq α]
    (s : Finset α) (x : α → K) (hx : Set.InjOn x s)
    (a b : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    (s.filter (fun i => a * x i + b = 0)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact hx (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (affine_root_unique hab (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)

theorem two_common_nonzero_of_four (x : Fin 4 → K) (hx : Function.Injective x)
    (a b c d : K) (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ i j : Fin 4, i ≠ j ∧ a * x i + b ≠ 0 ∧ c * x i + d ≠ 0 ∧
      a * x j + b ≠ 0 ∧ c * x j + d ≠ 0 := by
  classical
  let U := Finset.univ.filter (fun i => a * x i + b = 0)
  let V := Finset.univ.filter (fun i => c * x i + d = 0)
  have hu : U.card ≤ 1 := affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) _ _ hab
  have hv : V.card ≤ 1 := affine_roots_card_le_one _ _ (fun _ _ _ _ h => hx h) _ _ hcd
  have huv : (U ∪ V).card ≤ 2 := (Finset.card_union_le U V).trans (by omega)
  have hsub : U ∪ V ⊆ (Finset.univ : Finset (Fin 4)) := Finset.subset_univ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hfour : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
  have hgood : 1 < (Finset.univ \ (U ∪ V)).card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hgood
  have hi' : a * x i + b ≠ 0 ∧ c * x i + d ≠ 0 := by
    simpa [U, V] using hi
  have hj' : a * x j + b ≠ 0 ∧ c * x j + d ≠ 0 := by
    simpa [U, V] using hj
  exact ⟨i, j, hij, hi'.1, hi'.2, hj'.1, hj'.2⟩

private theorem three_rows (h2 : (2 : K) ≠ 0)
    (u₀ u₁ u₂ v₀ v₁ v₂ : K)
    (hp : 2 * u₂ + v₂ - 2 * (u₁ + v₁) + v₀ = 0)
    (hp' : 3 * u₂ + v₂ - 2 * (2 * u₁ + v₁) + u₀ + v₀ = 0)
    (hm : v₂ - 2 * (u₁ + v₁) + 2 * u₀ + v₀ = 0) :
    u₁ = u₀ ∧ u₂ = u₀ ∧ v₂ - 2 * v₁ + v₀ = 0 := by
  have hu : 2 * (u₂ - u₀) = 0 := by linear_combination hp - hm
  have hu₂ : u₂ = u₀ := sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_left h2)
  have hu' : 2 * (u₁ - u₀) = 0 := by linear_combination hp - hp' + hu₂
  have hu₁ : u₁ = u₀ := sub_eq_zero.mp ((mul_eq_zero.mp hu').resolve_left h2)
  refine ⟨hu₁, hu₂, ?_⟩
  linear_combination hp - 2 * hu₂ + 2 * hu₁

theorem four_rows_affine (h2 : (2 : K) ≠ 0) (U V : Fin 4 → K)
    (hp₀ : 2 * U 2 + V 2 - 2 * (U 1 + V 1) + V 0 = 0)
    (hp₀' : 3 * U 2 + V 2 - 2 * (2 * U 1 + V 1) + U 0 + V 0 = 0)
    (hm₀ : V 2 - 2 * (U 1 + V 1) + 2 * U 0 + V 0 = 0)
    (hp₁ : 2 * U 3 + V 3 - 2 * (U 2 + V 2) + V 1 = 0)
    (hp₁' : 3 * U 3 + V 3 - 2 * (2 * U 2 + V 2) + U 1 + V 1 = 0)
    (hm₁ : V 3 - 2 * (U 2 + V 2) + 2 * U 1 + V 1 = 0) :
    ∀ i j : Fin 4, U j * (i.val : K) + V j =
      U 0 * (i.val : K) + (V 1 - V 0) * (j.val : K) + V 0 := by
  obtain ⟨hu₁, hu₂, hv₂⟩ := three_rows h2 _ _ _ _ _ _ hp₀ hp₀' hm₀
  obtain ⟨_, hu₃, hv₃⟩ := three_rows h2 _ _ _ _ _ _ hp₁ hp₁' hm₁
  have hu₃' : U 3 = U 0 := hu₃.trans hu₁
  have hv₂' : V 2 = 2 * V 1 - V 0 := by linear_combination hv₂
  have hv₃' : V 3 = 3 * V 1 - 2 * V 0 := by linear_combination hv₃ + 2 * hv₂
  intro i j
  fin_cases j <;> simp only [Fin.reduceFinMk,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, hu₁, hu₂, hu₃', hv₂', hv₃'] <;> ring

end Field

theorem four_residues_injective {p : ℕ} (hp : 4 ≤ p) (r : ℤ) :
    Function.Injective (fun i : Fin 4 => ((r + i.val : ℤ) : ZMod p)) := by
  intro i j hij
  have hv : (i.val : ZMod p) = (j.val : ZMod p) := by
    simpa only [Int.cast_add, Int.cast_natCast, add_right_inj] using hij
  apply Fin.ext
  have h := congrArg ZMod.val hv
  simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hp),
    ZMod.val_natCast_of_lt (j.isLt.trans_le hp)] using h

theorem affine_int_roots_card_le {p : ℕ} (hp : p.Prime) (a b : ZMod p)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    ((Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)).filter
      (fun n : ℤ => a * (n : ZMod p) + b = 0)).card ≤ p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc : (Finset.Ico (0 : ℤ) (p : ℤ)).card = p := by simp
  refine le_trans ?_ (le_of_eq hc)
  apply Finset.card_le_card_of_injOn (fun n : ℤ => n / p)
  · intro n hn
    have hn' := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    apply Finset.mem_Ico.mpr
    refine ⟨Int.ediv_nonneg hn'.1 hpz.le, ?_⟩
    apply Int.ediv_lt_of_lt_mul hpz
    simpa only [pow_two, Nat.cast_mul] using hn'.2
  · intro n hn m hm hq
    have hnm : (n : ZMod p) = (m : ZMod p) := affine_root_unique hab
      (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2
    have hr := (ZMod.intCast_eq_intCast_iff' n m p).mp hnm
    have hnq := Int.emod_add_mul_ediv n (p : ℤ)
    have hmq := Int.emod_add_mul_ediv m (p : ℤ)
    change n / (p : ℤ) = m / (p : ℤ) at hq
    rw [hr, hq] at hnq
    omega

end PeriodicTilingThree

end OAI
