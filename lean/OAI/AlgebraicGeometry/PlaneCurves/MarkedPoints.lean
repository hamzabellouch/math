import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Choice of nine distinct marked parameters avoiding integral displacements
-/

section

/-!
# Delta selection with a finite forbidden set
-/
namespace Nagata.W06

/-- Every nonempty real interval contains a point outside any given finite set. -/
theorem exists_between_avoiding_finite {a b : ℝ} (hab : a < b)
    {F : Set ℝ} (hF : F.Finite) : ∃ x, a < x ∧ x < b ∧ x ∉ F := by
  induction F, hF using Set.Finite.induction_on generalizing a b with
  | empty =>
    obtain ⟨x, hax, hxb⟩ := exists_between hab
    exact ⟨x, hax, hxb, by simp⟩
  | @insert c F hc hF ih =>
    obtain ⟨x, hax, hxb, hxF⟩ := ih hab
    by_cases hxc : x = c
    · obtain ⟨y, hxy, hyb, hyF⟩ := ih hxb
      refine ⟨y, lt_trans hax hxy, hyb, ?_⟩
      intro hy
      rcases Set.mem_insert_iff.mp hy with hyc | hyF'
      · linarith
      · exact hyF hyF'
    · refine ⟨x, hax, hxb, ?_⟩
      intro hx
      rcases Set.mem_insert_iff.mp hx with hxc' | hxF'
      · exact hxc hxc'
      · exact hxF hxF' 

/-- The manuscript's strict delta slack survives deletion of a finite set. -/
theorem exists_delta_avoiding_finite {ρ B : ℝ} (hρ : 0 < ρ) (hB : ρ < B)
    {F : Set ℝ} (hF : F.Finite) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ < 1 / 2 ∧ ρ + Δ * ρ / 9 < B ∧ Δ ∉ F := by
  have hbound : 0 < min (1 / 2 : ℝ) (9 * (B - ρ) / ρ) := by
    apply lt_min
    · norm_num
    · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hB)) hρ
  obtain ⟨Δ, hΔ, hupper, havoid⟩ := exists_between_avoiding_finite hbound hF
  have hhalf : Δ < 1 / 2 := lt_of_lt_of_le hupper (min_le_left _ _)
  have hquot : Δ < 9 * (B - ρ) / ρ := lt_of_lt_of_le hupper (min_le_right _ _)
  have hprod : Δ * ρ < 9 * (B - ρ) := (lt_div_iff₀ hρ).mp hquot
  exact ⟨Δ, hΔ, hhalf, by linarith, havoid⟩

end Nagata.W06

end

section

/-!
# Explicit nine marked parameters
-/

namespace Nagata.W06

/-- Positive arithmetic-progression displacements of total `Δ`. -/
noncomputable def nineDisplacement (Δ : ℝ) (i : Fin 9) : ℝ := Δ * ((i.val : ℝ) + 1) / 45

/-- Exponents for the nine marked points in the manuscript. -/
noncomputable def markedExponent (Δ : ℝ) (i : Fin 9) : ℝ := 1 / 2 - nineDisplacement Δ i

theorem nineDisplacement_pos {Δ : ℝ} (hΔ : 0 < Δ) (i : Fin 9) :
    0 < nineDisplacement Δ i := by
  have hi : 0 < (i.val : ℝ) + 1 := by exact_mod_cast Nat.zero_lt_succ i.val
  exact div_pos (mul_pos hΔ hi) (by norm_num)

theorem nineDisplacement_lt {Δ : ℝ} (hΔ : 0 < Δ) (i : Fin 9) :
    nineDisplacement Δ i < Δ := by
  have hi : (i.val : ℝ) + 1 ≤ 9 := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hp := mul_nonneg (le_of_lt hΔ) (show 0 ≤ 9 - ((i.val : ℝ) + 1) by linarith)
  dsimp [nineDisplacement]
  nlinarith

theorem nineDisplacement_injective {Δ : ℝ} (hΔ : 0 < Δ) :
    Function.Injective (nineDisplacement Δ) := by
  intro i j hij
  dsimp [nineDisplacement] at hij
  have hmul : Δ * ((i.val : ℝ) + 1) = Δ * ((j.val : ℝ) + 1) := by linarith
  have hval := mul_left_cancel₀ (ne_of_gt hΔ) hmul
  apply Fin.ext
  exact_mod_cast (show (i.val : ℝ) = (j.val : ℝ) by linarith)

theorem sum_nineDisplacement (Δ : ℝ) :
    ∑ i : Fin 9, nineDisplacement Δ i = Δ := by
  norm_num [Fin.sum_univ_succ, nineDisplacement]
  ring

theorem markedExponent_pos {Δ : ℝ} (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2)
    (i : Fin 9) : 0 < markedExponent Δ i := by
  have h := nineDisplacement_lt hΔ i
  dsimp [markedExponent]
  linarith

theorem markedExponent_lt_half {Δ : ℝ} (hΔ : 0 < Δ) (i : Fin 9) :
    markedExponent Δ i < 1 / 2 := by
  have h := nineDisplacement_pos hΔ i
  dsimp [markedExponent]
  linarith

theorem markedExponent_injective {Δ : ℝ} (hΔ : 0 < Δ) :
    Function.Injective (markedExponent Δ) := by
  intro i j hij
  apply nineDisplacement_injective hΔ
  dsimp [markedExponent] at hij
  linarith

theorem sum_markedExponent_displacement (Δ : ℝ) :
    ∑ i : Fin 9, (1 / 2 - markedExponent Δ i) = Δ := by
  simpa only [markedExponent, sub_sub_cancel] using sum_nineDisplacement Δ

/-- The complete real-parameter existence assertion of `marked-parameters`. -/
theorem exists_marked_parameters {Δ : ℝ} (hΔ : 0 < Δ) (hhalf : Δ < 1 / 2) :
    ∃ x : Fin 9 → ℝ, Function.Injective x ∧
      (∀ i, 0 < x i ∧ x i < 1 / 2) ∧
      ∑ i : Fin 9, (1 / 2 - x i) = Δ := by
  refine ⟨markedExponent Δ, markedExponent_injective hΔ, ?_,
    sum_markedExponent_displacement Δ⟩
  intro i
  exact ⟨markedExponent_pos hΔ hhalf i, markedExponent_lt_half hΔ i⟩

/-- Exponents inside one open unit interval cannot differ by a nonzero integer. -/
theorem eq_of_sub_eq_integer {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (k : ℤ) (hk : x - y = k) : x = y := by
  have hlo : (-1 : ℝ) < (k : ℝ) := by linarith
  have hhi : (k : ℝ) < 1 := by linarith
  have hklo : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hkhi : k < (1 : ℤ) := by exact_mod_cast hhi
  have hk_nonneg : 0 ≤ k := by simpa using Int.add_one_le_iff.mpr hklo
  have hk_nonpos : k ≤ 0 := Int.lt_add_one_iff.mp hkhi
  have hkzero : k = 0 := le_antisymm hk_nonpos hk_nonneg
  rw [hkzero, Int.cast_zero] at hk
  linarith

/-- Distinct marked exponents are distinct modulo integer translation. -/
theorem markedExponent_difference_not_integer {Δ : ℝ} (hΔ : 0 < Δ)
    (hhalf : Δ < 1 / 2) {i j : Fin 9} (hij : i ≠ j) (k : ℤ) :
    markedExponent Δ i - markedExponent Δ j ≠ k := by
  intro hk
  apply hij
  apply markedExponent_injective hΔ
  have hi := markedExponent_lt_half hΔ i
  have hj := markedExponent_lt_half hΔ j
  exact eq_of_sub_eq_integer (markedExponent_pos hΔ hhalf i) (by linarith)
    (markedExponent_pos hΔ hhalf j) (by linarith) k hk

end Nagata.W06

end

end OAI
