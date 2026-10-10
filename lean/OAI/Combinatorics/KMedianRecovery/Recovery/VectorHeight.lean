import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Height
import OAI.Combinatorics.KMedianRecovery.Recovery.Grid

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility RationalHeight
open scoped Matrix BigOperators

def vectorHeight (n h a : ℕ) : ℕ := n*(h+a+1)
def quadHeight (n h a : ℕ) : ℕ := n*(a+vectorHeight n h a+1)
def rootHeight (n h a : ℕ) : ℕ := 2*quadHeight n h a+2*(5+n)+1
def incrementHeight (n h a : ℕ) : ℕ := n+1+rootHeight n h a+vectorHeight n h a

def storedShapeHeight (n T r : ℕ) : ℕ := T+2*r+(4+3*n+2*(T+1))

lemma mulVec_height {n h a : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (hH : ∀ i j,Height (H i j) h) (hv : ∀ i,Height (v i) a) (i : Fin n) :
    Height ((H *ᵥ v) i) (vectorHeight n h a) := by
  simpa only [Matrix.mulVec,dotProduct,Fintype.card_fin,vectorHeight] using
    RationalHeight.sum (fun j => H i j*v j) (h+a) (fun j => (hH i j).mul (hv j))

lemma rationalQuad_height {n h a : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (hH : ∀ i j,Height (H i j) h) (hv : ∀ i,Height (v i) a) :
    Height (rationalQuad H v) (quadHeight n h a) := by
  simpa only [rationalQuad,dotProduct,Fintype.card_fin,quadHeight] using
    RationalHeight.sum (fun i => v i*(H *ᵥ v) i) (a+vectorHeight n h a)
      (fun i => (hv i).mul (mulVec_height H v hH hv i))

lemma rationalRootUpper_height {q : ℚ} {b n : ℕ} (hq : Height q b) (hn : 0<n) :
    Height (rationalRootUpper (32*n) q) (2*b+2*(5+n)+1) := by
  have hD : 32*n≤2^(5+n) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left 32 (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  exact RationalHeight.sqrtFraction q.num.natAbs q.den (32*n) b (5+n)
    hq.1 hq.2 hD q.den_pos (by omega)

lemma center_increment_height {n h a : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (hH : ∀ i j,Height (H i j) h) (hv : ∀ i,Height (v i) a) (hn : 0<n) (i : Fin n) :
    Height ((1/(((n:ℚ)+1)*rationalRootUpper (32*n) (rationalQuad H v)))*(H *ᵥ v) i)
      (incrementHeight n h a) := by
  have hroot := rationalRootUpper_height (rationalQuad_height H v hH hv) hn
  have hd : Height ((n:ℚ)+1) (n+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using RationalHeight.natCast (n+1) (n+1)
      (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n+1)))
  simpa only [one_div,rootHeight,incrementHeight] using
    (hd.mul hroot).inv.mul (mulVec_height H v hH hv i)

lemma iterate_shape_Height (n T R r : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (hRr : R≤2^r) (t : ℕ) (ht : t≤T) (i j : Fin n) :
    Height ((iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j)
      (storedShapeHeight n T r) := by
  have hh := iterate_shape_height n T R r rows hn hR hRr t ht i j
  exact ⟨hh.2,hh.1.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [storedShapeHeight]; omega))⟩

theorem iterate_center_height (n T R r a : ℕ) (rows : List (Row n))
    (hn : 2≤n) (hR : 1≤R) (hRr : R≤2^r)
    (hrows : ∀ v∈rows, ∀ i,Height (v.coeff i) a) (t : ℕ) (ht : t≤T) (i : Fin n) :
    Height ((iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).center i)
      (t*(incrementHeight n (storedShapeHeight n T r) a+1)) := by
  induction t with
  | zero => exact RationalHeight.zero _
  | succ t ih =>
    have hc := ih (by omega)
    have hs := iterate_shape_Height n T R r rows hn hR hRr t (by omega)
    simp only [iterate,advance]
    split
    · exact hc.mono (Nat.mul_le_mul_right _ (by omega))
    · rename_i v hv
      split_ifs
      · exact hc.mono (Nat.mul_le_mul_right _ (by omega))
      · have hi := center_increment_height _ v.coeff hs
          (hrows v ((badRow_some _ _ _ hv).1)) (by omega) i
        have hh := hc.sub hi
        simp only [rationalStepCenter,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Fintype.card_fin]
        convert hh using 1
        ring

end MetricKMedianRecovery.Ellipsoid

end OAI
