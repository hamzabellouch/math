import OAI.NumberTheory.TotientAsymptotic.FordBandGeometry

namespace OAI

/-! Basic integer and band-product bounds for tuples satisfying Ford's published conditions. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_shift_pos {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (h : FordComparisonConditions b y S D r Y U t) (j : Fin b) :
    0 < t.left j-1 ∧ 0 < t.right j-1 := by
  have hl := (h.2.1 j).1.1.two_le
  have hr := (h.2.1 j).2.1.1.two_le
  omega

lemma ford_left_product_pos {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (h : FordComparisonConditions b y S D r Y U t) : 0 < shiftedProduct t.left :=
  Finset.prod_pos (fun j _ => (ford_shift_pos h j).1)

lemma ford_right_product_pos {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (h : FordComparisonConditions b y S D r Y U t) : 0 < shiftedProduct t.right :=
  Finset.prod_pos (fun j _ => (ford_shift_pos h j).2)

lemma ford_product_le_y {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hy : 0 ≤ y) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) : (shiftedProduct t.left:ℝ) ≤ y := by
  rcases hp with ⟨_,_,_,_,_,_,_,hD,_,_,hr,_⟩
  have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  calc
    (shiftedProduct t.left:ℝ) ≤ (D:ℝ)*(shiftedProduct t.left:ℝ) := by
      nlinarith [show (0:ℝ) ≤ shiftedProduct t.left from Nat.cast_nonneg _]
    _ ≤ y/r := by simpa only [Nat.cast_mul] using h.2.2.2.1
    _ ≤ y := div_le_self hy hr1

lemma ford_left_shift_le_y {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hy : 0 ≤ y) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) (j : Fin b) : (t.left j-1:ℕ) ≤ y := by
  have hn := Nat.le_of_dvd (ford_left_product_pos h) (shifted_factor_dvd t.left j)
  exact (show ((t.left j-1:ℕ):ℝ) ≤ shiftedProduct t.left by exact_mod_cast hn).trans
    (ford_product_le_y hy hp h)

lemma ford_right_product_le_y {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hy : 0 ≤ y) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) : (shiftedProduct t.right:ℝ) ≤ y := by
  rcases hp with ⟨_,_,_,_,_,_,_,_,_,_,hr,_⟩
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hrem1 : (1:ℝ) ≤ t.remainder := by exact_mod_cast h.1
  have he := congrArg (fun n : ℕ => (n:ℝ)) h.2.2.1
  simp only [Nat.cast_mul] at he
  have hsize : (t.remainder:ℝ)*(shiftedProduct t.right:ℝ) ≤ y/r := by
    rw [← he]
    simpa only [Nat.cast_mul] using h.2.2.2.1
  calc
    (shiftedProduct t.right:ℝ) ≤ (t.remainder:ℝ)*(shiftedProduct t.right:ℝ) := by
      nlinarith [show (0:ℝ) ≤ shiftedProduct t.right from Nat.cast_nonneg _]
    _ ≤ y/r := hsize
    _ ≤ y := div_le_self hy hr1

lemma ford_right_shift_le_y {b D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hy : 0 ≤ y) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) (j : Fin b) : (t.right j-1:ℕ) ≤ y := by
  have hn := Nat.le_of_dvd (ford_right_product_pos h) (shifted_factor_dvd t.right j)
  exact (show ((t.right j-1:ℕ):ℝ) ≤ shiftedProduct t.right by exact_mod_cast hn).trans
    (ford_right_product_le_y hy hp h)

lemma ford_common_band {b D r : ℕ} {y S Z V : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) (hZ : Y b ≤ Z) :
    (∏ j,partBetween (t.left j-1) Z V)=∏ j,partBetween (t.right j-1) Z V := by
  rcases hp with ⟨_,_,_,_,_,_,_,hD,_,hDs,_,_⟩
  let hf : PairedFactors b := (fun j => t.left j-1,fun j => t.right j-1)
  exact common_band_product hf (by omega) h.1.ne'
    (fun j => (ford_shift_pos h j).1.ne') (fun j => (ford_shift_pos h j).2.ne')
    h.2.2.1 (hDs.trans hZ) (h.2.2.2.2.1.trans hZ)

end TotientAsymptotic

end

end OAI
