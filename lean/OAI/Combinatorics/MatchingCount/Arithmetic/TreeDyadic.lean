import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Related2
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction Polynomial

def level (x : ℕ×Fraction) : ℕ := min x.1 ((x.2.1/x.2.2).size-1)
def levelRealizer : Realizer level := composition (pair first
  (composition (composition (composition second quotient) bitSize) predecessor)) minNat
lemma polynomial_level : PolynomialTime levelRealizer := by
  exact polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_second
      polynomial_quotient) polynomial_bitSize) polynomial_predecessor)) polynomial_minNat
lemma findGreatest_lt_size (H s : ℕ) : Nat.findGreatest (fun k=>k<s) H=min H (s-1) := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨min_le_left _ _,?_,?_⟩
  · intro h
    have hle:=min_le_right H (s-1)
    omega
  · intro k hk hkH hks
    have hmin:=le_min hkH (show k ≤ s-1 by omega)
    omega
lemma level_val (H : ℕ) (x : Fraction) : level (H,x)=(NumberedHierarchy.level H (val x)).val := by
  have hp : (fun k=>(2:ℚ)^k≤val x)=(fun k=>k<(x.1/x.2).size) := by
    funext k
    apply propext
    rw [Nat.lt_size]
    rw [←Rat.natFloor_natCast_div_natCast]
    have h:=Nat.le_floor_iff' (R:=ℚ) (n:=2^k) (a:=val x) (by positivity)
    simpa only [val,Nat.cast_pow,Nat.cast_ofNat] using h.symm
  simp only [NumberedHierarchy.level,level,hp,findGreatest_lt_size]
lemma level_repr (H : ℕ) (q : ℚ) (hq : 0≤q) :
    level (H,TreeFraction.repr q)=(NumberedHierarchy.level H q).val := by
  rw [level_val,TreeFraction.val_repr hq]

def threshold (x : List Bool×ℕ) : Fraction := (bitDenominator (x.1.take x.2),1)
def thresholdRealizer : Realizer threshold := pair (composition takeFast bitDenominatorRealizer) (constant 1)
lemma polynomial_threshold : PolynomialTime thresholdRealizer := by
  unfold thresholdRealizer
  exact polynomial_pair (polynomial_composition polynomial_takeFast polynomial_bitDenominator) (polynomial_constant 1)
lemma threshold_repr (xs : List Bool) (k : ℕ) (hk : k≤xs.length) :
    threshold (xs,k)=TreeFraction.repr ((2:ℚ)^k) := by
  simp only [threshold,bitDenominator_eq,List.length_take,min_eq_left hk]
  have h : val ((2^k,1):Fraction)=(2:ℚ)^k := by simp [val]
  rw [←h,←normalize_repr]
  simp [TreeFraction.normalize]
end MatchingFPRAS.ExecutableHierarchy

end OAI
