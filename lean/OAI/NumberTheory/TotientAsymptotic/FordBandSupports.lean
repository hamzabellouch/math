import OAI.NumberTheory.TotientAsymptotic.FordTupleFactors
import OAI.NumberTheory.TotientAsymptotic.CollisionBandData

namespace OAI

/-! Support, equality and squarefreeness of the actual bands of a Ford tuple. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_scale_bounds {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ}
    (h : FordComparisonParameters b y S D r Y U) : 1 < S ∧ 1 ≤ B S := by
  have hS := h.2.2.1
  have hS1 : 1 < S := (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hS
  have hlog := Real.log_le_log (Real.exp_pos (Real.exp 1)) hS
  rw [Real.log_exp] at hlog
  have hB := Real.log_le_log (Real.exp_pos 1) hlog
  rw [Real.log_exp] at hB
  exact ⟨hS1,hB⟩

lemma two_le_of_one_lt_largest {n : ℕ} (h : 1 < largestPrimeFactor n) : 2 ≤ n := by
  by_contra hn
  have hn : n=0 ∨ n=1 := by omega
  rcases hn with rfl|rfl <;> norm_num [largestPrimeFactor] at h

def fordBand {b k : ℕ} (hk : k ≤ b) (t : ShiftedPair b) (Y : ℕ → ℝ) : PairedFactors k :=
  (fun j => partBetween (t.left (Fin.castLE hk j)-1) (Y k) (Y (k-1)),
   fun j => partBetween (t.right (Fin.castLE hk j)-1) (Y k) (Y (k-1)))

lemma ford_band_tail {b k D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t)
    (j : Fin b) (hj : k ≤ j.val) :
    partBetween (t.left j-1) (Y k) (Y (k-1))=1 ∧
      partBetween (t.right j-1) (Y k) (Y (k-1))=1 := by
  obtain ⟨_,_,_,_,hl,_,hr,_,_⟩ := h.2.1 j
  have hY := ford_cutoff_antitone hp hj j.isLt.le
  exact ⟨partBetween_eq_one_of_largest_le (hl.trans hY),
    partBetween_eq_one_of_largest_le (hr.trans hY)⟩

lemma ford_band_product {b k D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hk : k ≤ b) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    pairedProduct (fordBand hk t Y)=partBetween (shiftedProduct t.left) (Y k) (Y (k-1)) := by
  rw [shiftedProduct,partBetween_prod _ _ (fun j _ => (ford_shift_pos h j).1.ne')]
  exact (fin_prod_initial hk _ (fun j hj => (ford_band_tail hp h j hj).1)).symm

lemma ford_band_product_eq {b k D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hk : k ≤ b) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    pairedProduct (fordBand hk t Y)=∏ j,(fordBand hk t Y).2 j := by
  have he := ford_common_band (V:=Y (k-1)) hp h (ford_cutoff_antitone hp hk le_rfl)
  rw [fin_prod_initial hk _ (fun j hj => (ford_band_tail hp h j hj).1),
    fin_prod_initial hk _ (fun j hj => (ford_band_tail hp h j hj).2)] at he
  exact he

lemma ford_band_squarefree {b k D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hk : k ≤ b) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) : Squarefree (pairedProduct (fordBand hk t Y)) := by
  rw [ford_band_product hk hp h]
  apply partBetween_squarefree (ford_left_product_pos h).ne'
  intro p hprime hlarge
  apply h.2.2.2.2.2.2 p hprime
  exact (ford_cutoff_antitone hp hk le_rfl).trans_lt hlarge

end TotientAsymptotic

end

end OAI
