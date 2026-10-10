import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelTable
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineScheduleNat

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

def natCeil (x : Fraction) : ℕ := (x.1+x.2-1)/x.2
def natCeilRealizer : Realizer natCeil :=
  (composition (pair (composition (composition (pair first second) TreeTyped.add) predecessor) second) quotient).congr (fun _=>rfl)
lemma polynomial_natCeil : PolynomialTime natCeilRealizer := by
  unfold natCeilRealizer; apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_quotient
  tree_cost
lemma natCeil_eq (x : Fraction) : natCeil x=⌈val x⌉₊ := by
  by_cases hd : x.2=0
  · simp [natCeil,val,hd]
  have hd' : (0:ℚ)<x.2 := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have h (m : ℕ) : ⌈val x⌉₊ ≤ m ↔ natCeil x ≤ m := by
    rw [Nat.ceil_le]
    unfold val natCeil
    rw [div_le_iff₀ hd',←Nat.cast_mul,Nat.cast_le,Nat.div_le_iff_le_mul (Nat.pos_of_ne_zero hd)]
    omega
  exact Nat.le_antisymm ((h _).mp le_rfl) ((h _).mpr le_rfl)
lemma natCeil_repr (q : ℚ) (hq : 0≤q) : natCeil (repr q)=⌈q⌉₊ := by
  rw [natCeil_eq,val_repr hq]

def inverse (x : Fraction) : Fraction := normalize (x.2,x.1)
def inverseRealizer : Realizer inverse := composition (pair second first) normalizeRealizer
lemma polynomial_inverse : PolynomialTime inverseRealizer := by
  unfold inverseRealizer; exact polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_normalize
lemma inverse_repr (q : ℚ) (hq : 0≤q) : inverse (repr q)=repr q⁻¹ := by
  unfold inverse
  rw [normalize_repr]
  congr 1
  change (q.den:ℚ)/q.num.natAbs=q⁻¹
  calc
    _ = (val (repr q))⁻¹ := by simp [val,repr]
    _ = q⁻¹ := by rw [val_repr hq]
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

abbrev RootInput := ℕ×List Bool
def rootCandidate (x : RootInput×ℕ) : Bool := decide (x.1.1<(x.2+1)^2)
def rootCandidateRealizer : Realizer rootCandidate :=
  (composition (pair first.fst (composition (composition second successor) (fixedPower 2))) TreeTyped.less).congr (fun _=>rfl)
lemma polynomial_rootCandidate : PolynomialTime rootCandidateRealizer := by
  unfold rootCandidateRealizer Realizer.fst; apply polynomial_congr
  have := polynomial_fixedPower 2
  have := polynomial_successor
  tree_cost

def findRoot (x : RootInput) : ℕ :=
  listMin ((List.range (x.2.length+1)).filter (fun i=>rootCandidate (x,i)),x.2.length)
def findRootRealizer : Realizer findRoot := by
  let B : Realizer (fun x : RootInput=>x.2.length) := composition second listLength
  let R := composition (composition B successor) range
  let F := composition (pair identity R) (filterWith rootCandidateRealizer)
  exact (composition (pair F B) listMinRealizer).congr (fun _=>rfl)
lemma polynomial_findRoot : PolynomialTime findRootRealizer := by
  unfold findRootRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_listMin
  apply polynomial_pair _ (polynomial_composition polynomial_second polynomial_listLength)
  apply polynomial_composition _ (polynomial_filterWithList polynomial_rootCandidate)
  apply polynomial_pair polynomial_identity
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_second polynomial_listLength) polynomial_successor)
    (X+1)
  intro x
  have h:=list_length_le_weight x.2
  change x.2.length+1≤(X+1).eval (weight x)
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  rw [weight_prod]
  omega
lemma findRoot_eq (n : ℕ) (fuel : List Bool) (hf : n.sqrt≤fuel.length) :
    findRoot (n,fuel)=n.sqrt := by
  apply Nat.le_antisymm
  · apply listMin_le
    simp only [List.mem_filter,List.mem_range,rootCandidate,decide_eq_true_eq]
    exact ⟨by omega,by simpa [pow_two,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n⟩
  · apply le_listMin hf
    intro i hi
    simp only [List.mem_filter,List.mem_range,rootCandidate,decide_eq_true_eq,pow_two] at hi
    have h:=Nat.sqrt_lt.mpr hi.2
    omega
end MatchingFPRAS.OnlineSchedule

end OAI
