import OAI.Analysis.MarkovType.CoefficientGrid
import OAI.Analysis.MarkovType.FiniteRamsey
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_row_sum_le_card {m : ℕ} (a : Fin m → ℝ) (y : Fin m → Y)
    (ha : ∀ i, |a i| ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) :
    ‖∑ i, a i • y i‖ ≤ (m : ℝ) := by
  calc
    ‖∑ i, a i • y i‖ ≤ ∑ i, ‖a i • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |a i| * ‖y i‖ ≤ |a i| * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
        _ ≤ 1 := by simpa only [mul_one] using ha i
    _ = (m : ℝ) := by simp

theorem abs_norm_row_sum_sub_le {m : ℕ} (a b : Fin m → ℝ)
    (y : Fin m → Y) (hy : ∀ i, ‖y i‖ ≤ 1) (ε : ℝ)
    (hab : ∀ i, |a i - b i| ≤ ε) :
    |‖∑ i, a i • y i‖ - ‖∑ i, b i • y i‖| ≤ (m : ℝ) * ε := by
  calc
    |‖∑ i, a i • y i‖ - ‖∑ i, b i • y i‖| ≤
        ‖(∑ i, a i • y i) - ∑ i, b i • y i‖ := abs_norm_sub_norm_le _ _
    _ = ‖∑ i, (a i - b i) • y i‖ := by
      simp only [sub_smul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖(a i - b i) • y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, ε := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |a i - b i| * ‖y i‖ ≤ |a i - b i| * 1 :=
          mul_le_mul_of_nonneg_left (hy i) (abs_nonneg _)
        _ ≤ ε := by simpa only [mul_one] using hab i
    _ = (m : ℝ) * ε := by simp

private abbrev RowCoefficientGrid (k m : ℕ) := Fin m → Fin (2 * k ^ 2 + 1)

private abbrev RowPalette (k m : ℕ) := RowCoefficientGrid k m → Fin (k * m + 1)

private def boundedNormBin (k m : ℕ) (z : ℝ) (hz : z ≤ (m : ℝ)) :
    Fin (k * m + 1) :=
  ⟨⌊(k : ℝ) * z⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le (by
    simpa only [Nat.cast_mul] using
      mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg k)))⟩

private theorem boundedNormBin_close {k m : ℕ} (hk : 0 < k)
    {z w : ℝ} (hz0 : 0 ≤ z) (hw0 : 0 ≤ w)
    {hz : z ≤ (m : ℝ)} {hw : w ≤ (m : ℝ)}
    (h : boundedNormBin k m z hz = boundedNormBin k m w hw) :
    |z - w| ≤ 1 / (k : ℝ) := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have heq : ⌊(k : ℝ) * z⌋₊ = ⌊(k : ℝ) * w⌋₊ := congrArg Fin.val h
  have hzLower := Nat.floor_le (mul_nonneg hkR.le hz0)
  have hwLower := Nat.floor_le (mul_nonneg hkR.le hw0)
  have hzUpper := Nat.lt_floor_add_one ((k : ℝ) * z)
  have hwUpper := Nat.lt_floor_add_one ((k : ℝ) * w)
  rw [heq] at hzLower hzUpper
  have hzw : z - w ≤ 1 / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  have hwz : w - z ≤ 1 / (k : ℝ) := by
    apply (le_div_iff₀ hkR).2
    nlinarith
  exact abs_le.mpr ⟨by linarith, hzw⟩

theorem exists_homogeneous_rows (k : ℕ) (hk : 0 < k) :
    ∃ B : ℕ, k ≤ B ∧ k ^ 3 ≤ B ∧
      ∀ y : Fin B → Y, (∀ i, ‖y i‖ ≤ 1) →
        ∃ e : Fin k ↪o Fin B,
          ∀ (m : ℕ) (_hm : m ≤ k) (a : Fin m → ℝ), (∀ i, |a i| ≤ 1) →
            ∀ s t : Fin m ↪o Fin k,
              |‖∑ i, a i • y (e (s i))‖ - ‖∑ i, a i • y (e (t i))‖| ≤
                3 / (k : ℝ) := by
  classical
  let colors : Fin (k + 1) → ℕ := fun m => Fintype.card (RowPalette k m.val)
  have hcolors : ∀ m, 0 < colors m := by
    intro m
    change 0 < Fintype.card (RowPalette k m.val)
    let : Nonempty (RowPalette k m.val) :=
      ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩⟩
    exact Fintype.card_pos
  obtain ⟨B, hBbound, hB⟩ :=
    finite_ordered_simultaneous_ramsey k (k ^ 3) colors hcolors
  refine ⟨B, (le_max_left _ _).trans hBbound,
    (le_max_right _ _).trans hBbound, ?_⟩
  intro y hy
  let rawColor : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → RowPalette k m.val :=
    fun m u g => boundedNormBin k m.val
      ‖∑ i, coefficientGridValue k (g i) • y (u i)‖
      (norm_row_sum_le_card (fun i => coefficientGridValue k (g i))
        (fun i => y (u i)) (fun i => abs_coefficientGridValue_le k hk (g i))
        (fun i => hy (u i)))
  let χ : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → Fin (colors m) :=
    fun m u => Fintype.equivFin (RowPalette k m.val) (rawColor m u)
  obtain ⟨e, he⟩ := hB χ
  refine ⟨e, ?_⟩
  intro m hm a ha s t
  let arity : Fin (k + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hencoded :
      Fintype.equivFin (RowPalette k m) (rawColor arity (s.trans e)) =
        Fintype.equivFin (RowPalette k m) (rawColor arity (t.trans e)) :=
    he arity s t
  have hcolor : rawColor arity (s.trans e) = rawColor arity (t.trans e) :=
    (Fintype.equivFin (RowPalette k m)).injective hencoded
  let g : RowCoefficientGrid k m := fun i =>
    Classical.choose (exists_coefficientGrid_approx k hk (a i) (ha i))
  have hg : ∀ i, |a i - coefficientGridValue k (g i)| ≤ 1 / (k : ℝ) ^ 2 := by
    intro i
    exact Classical.choose_spec (exists_coefficientGrid_approx k hk (a i) (ha i))
  have hmiddle :
      |‖∑ i, coefficientGridValue k (g i) • y (e (s i))‖ -
        ‖∑ i, coefficientGridValue k (g i) • y (e (t i))‖| ≤ 1 / (k : ℝ) := by
    exact boundedNormBin_close (m := m) hk (norm_nonneg _) (norm_nonneg _)
      (congrFun hcolor g)
  have hleft := abs_norm_row_sum_sub_le a (fun i => coefficientGridValue k (g i))
    (fun i => y (e (s i))) (fun i => hy (e (s i))) (1 / (k : ℝ) ^ 2) hg
  have hright := abs_norm_row_sum_sub_le a (fun i => coefficientGridValue k (g i))
    (fun i => y (e (t i))) (fun i => hy (e (t i))) (1 / (k : ℝ) ^ 2) hg
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hmR : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hm
  have hbudget : (m : ℝ) * (1 / (k : ℝ) ^ 2) ≤ 1 / (k : ℝ) := by
    calc
      (m : ℝ) * (1 / (k : ℝ) ^ 2) ≤ (k : ℝ) * (1 / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hmR (div_nonneg zero_le_one (sq_nonneg _))
      _ = 1 / (k : ℝ) := by field_simp [hkne]
  have hthree : (3 : ℝ) / (k : ℝ) = 3 * (1 / (k : ℝ)) := by ring
  rw [hthree]
  obtain ⟨hleftLower, hleftUpper⟩ := abs_le.mp hleft
  obtain ⟨hrightLower, hrightUpper⟩ := abs_le.mp hright
  obtain ⟨hmiddleLower, hmiddleUpper⟩ := abs_le.mp hmiddle
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end MarkovSuperreflexivity

end OAI
