import Mathlib
import OAI.RepresentationTheory.PartialPermutation.DiagonalBounds
import OAI.RepresentationTheory.PartialPermutation.Truncation

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def transposeCellsEquiv (μ : YoungDiagram) : μ.cells ≃o μ.transpose.cells where
  toFun x := ⟨x.1.swap, by simpa only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose,
    Prod.swap_swap] using x.2⟩
  invFun x := ⟨x.1.swap, YoungDiagram.mem_transpose.mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intro x y; exact ⟨fun h => ⟨h.2,h.1⟩,fun h => ⟨h.2,h.1⟩⟩

lemma standardCount_transpose (μ : YoungDiagram) : standardCount μ.transpose = standardCount μ :=
  (Fintype.card_congr (fillingCongr (transposeCellsEquiv μ))).symm

lemma card_transpose (μ : YoungDiagram) : μ.transpose.cells.card = μ.cells.card := by
  simpa only [Fintype.card_coe] using (Fintype.card_congr (transposeCellsEquiv μ).toEquiv).symm

lemma maxLine_transpose (μ : YoungDiagram) : maxLine μ.transpose = maxLine μ := by
  simp only [maxLine, YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose, max_comm]

lemma deficit_transpose (μ : YoungDiagram) : deficit μ.transpose = deficit μ := by
  simp only [deficit, card_transpose, maxLine_transpose]

lemma two_pow_le_centralBinom (b : ℕ) : 2^b ≤ (2*b).choose b := by
  change 2^b ≤ Nat.centralBinom b
  induction b with
  | zero => simp
  | succ b ih =>
    have he := Nat.succ_mul_centralBinom_succ b
    have hstep : 2 * Nat.centralBinom b ≤ Nat.centralBinom (b+1) := by
      by_contra h
      have hh := Nat.mul_lt_mul_of_pos_left (show Nat.centralBinom (b+1) < 2*Nat.centralBinom b by omega)
        (Nat.succ_pos b)
      nlinarith
    calc
      2^(b+1) = 2 * 2^b := by rw [pow_succ']
      _ ≤ 2 * Nat.centralBinom b := Nat.mul_le_mul_left _ ih
      _ ≤ _ := hstep

lemma tail_power_lower_bound_oriented (μ : YoungDiagram)
    (hor : μ.colLen 0 ≤ μ.rowLen 0) : 2^(deficit μ/8) ≤ standardCount μ := by
  have hL : maxLine μ = μ.rowLen 0 := max_eq_left hor
  by_cases hsmall : 4*maxLine μ ≤ μ.cells.card
  · apply le_trans (Nat.pow_le_pow_right (by omega) (show deficit μ/8 ≤
        μ.cells.card-(2*maxLine μ-1) by unfold deficit; omega))
      (width_height_power_lower_bound μ)
  · let b := min (deficit μ) (μ.rowLen 0/2)
    have hb₁ : b ≤ deficit μ := min_le_left _ _
    have hb₂ : b ≤ μ.rowLen 0/2 := min_le_right _ _
    have hba : b ≤ min (μ.rowLen 0) (μ.cells.card-μ.rowLen 0) := by
      rw [deficit,hL] at hb₁
      exact le_min (by omega) hb₁
    have hkb : deficit μ/8 ≤ b := by
      have hc := topRow_le_card μ
      dsimp [b]
      apply le_min
      · exact Nat.div_le_self _ _
      · rw [hL] at hsmall
        unfold deficit
        rw [hL]
        omega
    calc
      2^(deficit μ/8) ≤ 2^b := Nat.pow_le_pow_right (by omega) hkb
      _ ≤ (2*b).choose b := two_pow_le_centralBinom b
      _ ≤ (μ.rowLen 0).choose b := Nat.choose_le_choose b (by omega)
      _ ≤ standardCount μ := binomial_lower_bound μ b hba

lemma tail_power_lower_bound (μ : YoungDiagram) : 2^(deficit μ/8) ≤ standardCount μ := by
  by_cases h : μ.colLen 0 ≤ μ.rowLen 0
  · exact tail_power_lower_bound_oriented μ h
  · have hh := tail_power_lower_bound_oriented μ.transpose (by
      simpa only [YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose] using le_of_not_ge h)
    simpa only [deficit_transpose, standardCount_transpose] using hh

lemma longest_binomial_lower_bound (μ : YoungDiagram) (b : ℕ)
    (hb : b ≤ min (maxLine μ) (deficit μ)) :
    (maxLine μ).choose b ≤ standardCount μ := by
  by_cases h : μ.colLen 0 ≤ μ.rowLen 0
  · have he : maxLine μ=μ.rowLen 0 := max_eq_left h
    rw [he]
    exact binomial_lower_bound μ b (by simpa only [deficit,he] using hb)
  · have hb' : b ≤ min (μ.transpose.rowLen 0)
        (μ.transpose.cells.card - μ.transpose.rowLen 0) := by
      simpa only [deficit,maxLine,max_eq_right (le_of_not_ge h),
        card_transpose,YoungDiagram.rowLen_transpose] using hb
    simpa only [YoungDiagram.rowLen_transpose,standardCount_transpose,
      maxLine,max_eq_right (le_of_not_ge h)] using binomial_lower_bound μ.transpose b hb'

lemma linear_le_choose (a k : ℕ) (hk : 0 < k) (hka : k ≤ a) : a-k+1 ≤ a.choose k := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hka
  simp only [Nat.add_sub_cancel_left]
  induction r with
  | zero => simp
  | succ r ih =>
    have hk' : k-1 ≤ k+r := by omega
    have hpos := Nat.choose_pos hk'
    have he : (k+(r+1)).choose k = (k+r).choose (k-1)+(k+r).choose k := by
      have h := Nat.choose_succ_succ (k+r) (k-1)
      simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel (show 1≤k by omega), Nat.add_assoc] using h
    rw [he]
    omega

lemma fixed_deficit_growth (μ : YoungDiagram) (hk : 0 < deficit μ)
    (hlarge : 2*deficit μ ≤ μ.cells.card) :
    μ.cells.card-2*deficit μ+1 ≤ standardCount μ := by
  have hLle : maxLine μ ≤ μ.cells.card := by
    apply max_le
    · exact topRow_le_card μ
    · have h:=topRow_le_card μ.transpose
      simpa only [YoungDiagram.rowLen_transpose,card_transpose] using h
  have hkL : deficit μ ≤ maxLine μ := by unfold deficit at *; omega
  have he : μ.cells.card-2*deficit μ=maxLine μ-deficit μ := by
    unfold deficit at *; omega
  rw [he]
  exact (linear_le_choose _ _ hk hkL).trans
    (longest_binomial_lower_bound μ (deficit μ) (le_min hkL le_rfl))

end
end Tableau
end PartialPermutation

end

end OAI
