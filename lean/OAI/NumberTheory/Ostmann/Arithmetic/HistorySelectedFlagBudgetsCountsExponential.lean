import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgetsCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgetsNumerics

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagBudgets
open Construction HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairRows HistoryPairRepresentatives HistoryPairFlags
open HistorySelectedPairDerivativeCounts

def countQuadraticCoefficient (k : ℕ) : ℝ :=
  8*(historyCostCoefficient k:ℝ)+4*(countCoefficient k:ℝ)+
    (2*(countCoefficient k:ℝ))^2+3

def countExponent (k : ℕ) : ℝ := countQuadraticCoefficient k+2

theorem countQuadraticCoefficient_pos (k : ℕ) : 0 < countQuadraticCoefficient k := by
  unfold countQuadraticCoefficient
  positivity

theorem countExponent_pos (k : ℕ) : 0 < countExponent k := by
  have h := countQuadraticCoefficient_pos k
  unfold countExponent
  linarith

private theorem count_quadratic_le_exp (k : ℕ) {m x : ℝ} (hm : 0 ≤ m)
    (hx : x ≤ countQuadraticCoefficient k*(m+1)^2) :
    x ≤ Real.exp (countExponent k*(m+1)) := by
  have h := quadratic_prefactor_le_exp (H:=0) (countQuadraticCoefficient_pos k).le
    (by linarith : 1 ≤ m+1)
  simp only [Real.exp_zero,mul_one,add_zero] at h
  exact hx.trans h

private theorem count_linear_le_exp (k : ℕ) {D m x : ℝ}
    (hD : 0 ≤ D) (hDk : D ≤ countQuadraticCoefficient k) (hm : 0 ≤ m)
    (hx : x ≤ D*(m+1)) : x ≤ Real.exp (countExponent k*(m+1)) := by
  apply count_quadratic_le_exp k hm
  have hM : m+1 ≤ (m+1)^2 := by nlinarith
  exact hx.trans ((mul_le_mul_of_nonneg_left hM hD).trans
    (mul_le_mul_of_nonneg_right hDk (sq_nonneg _)))

theorem four_degreeBudget_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) :
    ((4*degreeBudget h g:ℕ):ℝ) ≤ Real.exp (countExponent k*(m+1)) := by
  apply count_linear_le_exp k (D:=8*(historyCostCoefficient k:ℝ)) (by positivity)
    (by
      unfold countQuadraticCoefficient
      have hC := Nat.cast_nonneg (α:=ℝ) (countCoefficient k)
      nlinarith [sq_nonneg (2*(countCoefficient k:ℝ))]) hm
  have hd := degreeBudget_le_real hh hg hl
  have hs := mul_le_mul_of_nonneg_left (show (b:ℝ)+1 ≤ m+1 by linarith)
    (by positivity : 0 ≤ 8*(historyCostCoefficient k:ℝ))
  push_cast
  nlinarith

theorem degreeBudget_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) :
    (degreeBudget h g:ℝ) ≤ Real.exp (countExponent k*(m+1)) := by
  apply le_trans _ (four_degreeBudget_le_exp hh hg hl hm hb)
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) (degreeBudget h g)]

theorem polynomial_degree_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (gs : g.Supported V outside)
    (r : Representative h g) (i : Index h g r) :
    ((polynomial h g hs gs r i).totalDegree:ℝ) ≤ Real.exp (countExponent k*(m+1)) :=
  (Nat.cast_le.mpr (polynomial_degree h g hs gs r i)).trans
    (four_degreeBudget_le_exp hh hg hl hm hb)

private theorem occurrence_bound_le_exp (k b : ℕ) {m : ℝ}
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) :
    2*(countCoefficient k:ℝ)*(b+1) ≤ Real.exp (countExponent k*(m+1)) := by
  apply count_linear_le_exp k (D:=2*(countCoefficient k:ℝ)) (by positivity) _ hm
    (mul_le_mul_of_nonneg_left (by linarith : (b:ℝ)+1 ≤ m+1) (by positivity))
  unfold countQuadraticCoefficient
  have hC := Nat.cast_nonneg (α:=ℝ) (countCoefficient k)
  have hH := Nat.cast_nonneg (α:=ℝ) (historyCostCoefficient k)
  nlinarith [sq_nonneg (2*(countCoefficient k:ℝ))]

theorem occurrences_card_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) :
    (Fintype.card (Occurrences h g):ℝ) ≤ Real.exp (countExponent k*(m+1)) :=
  (occurrences_card_le_real hh hg hl).trans (occurrence_bound_le_exp k b hm hb)

theorem fiber_card_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) (r : Representative h g) :
    (Fintype.card (Fiber h g r):ℝ) ≤ Real.exp (countExponent k*(m+1)) :=
  (fiber_card_le_real hh hg hl r).trans (occurrence_bound_le_exp k b hm hb)

theorem representative_card_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) :
    (Fintype.card (Representative h g):ℝ) ≤ Real.exp (countExponent k*(m+1)) :=
  (representative_card_le_real hh hg hl).trans (occurrence_bound_le_exp k b hm hb)

theorem index_card_le_exp {b k l : ℕ} {h g : History l} {m : ℝ}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) (hl : l ≤ k)
    (hm : 0 ≤ m) (hb : (b:ℝ) ≤ m) (r : Representative h g) :
    (Fintype.card (Index h g r):ℝ) ≤ Real.exp (countExponent k*(m+1)) := by
  apply count_quadratic_le_exp k hm
  let N : ℝ := 2*(countCoefficient k:ℝ)
  let M : ℝ := m+1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hM0 : 0 ≤ M := by dsimp [M]; linarith
  have hM2 : M ≤ M^2 := by dsimp [M]; nlinarith
  have hNM : N*((b:ℝ)+1) ≤ N*M :=
    mul_le_mul_of_nonneg_left (by dsimp [M]; linarith) hN
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ N*((b:ℝ)+1)) hNM 2
  have hD : 2*N+N^2 ≤ countQuadraticCoefficient k := by
    dsimp [N,countQuadraticCoefficient]
    have hH := Nat.cast_nonneg (α:=ℝ) (historyCostCoefficient k)
    nlinarith
  calc
    _ ≤ 2*(N*((b:ℝ)+1))+(N*((b:ℝ)+1))^2 := index_card_le_real hh hg hl r
    _ ≤ 2*(N*M)+(N*M)^2 := by nlinarith
    _ = 2*N*M+N^2*M^2 := by ring
    _ ≤ 2*N*M^2+N^2*M^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hM2 (by positivity : 0 ≤ 2*N)) le_rfl
    _ = (2*N+N^2)*M^2 := by ring
    _ ≤ countQuadraticCoefficient k*M^2 := mul_le_mul_of_nonneg_right hD (sq_nonneg M)

end Ostmann.Arithmetic.HistorySelectedFlagBudgets

end

end OAI
