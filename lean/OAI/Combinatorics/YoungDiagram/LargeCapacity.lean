import OAI.Combinatorics.YoungDiagram.Capacity

namespace OAI

/- The opposite-prefix area bound implies the numerical band criterion for large parameters. -/
namespace ArithmeticTensorSquares.Capacity
open scoped BigOperators

/-- Nat truncated subtraction/division equals max(0,floor((h-d)/2))
for the manuscript's nonnegative integral heights. -/
def attachmentCapacity (height : Nat → Nat) (d q : Nat) : Nat :=
  ∑ i ∈ Finset.range q, (height i - d) / 2

/-- Exactly the three numeric inequalities of prop:band-test, in one orientation.
K=2M-1; height=column lengths and width=row lengths. -/
def BandTest (height width : Nat → Nat) (M r : Nat) : Prop :=
  ∃ d q : Nat, 1 ≤ d ∧ d ≤ 4 ∧ q ≤ 8 ∧
    2*M-1 ≤ ∑ i ∈ Finset.range d, width i ∧
    d*q+7+d ≤ 2*M-1 ∧ r ≤ attachmentCapacity height d q

lemma height_floor_bound (x : Nat) : x ≤ 2*((x-4)/2)+5 := by omega

lemma prefix_eight_bound (height : Nat → Nat) (r : Nat) (_hr : 0 < r)
    (hfail : attachmentCapacity height 4 8 < r) :
    (∑ i ∈ Finset.range 8, height i) ≤ 2*r+38 := by
  have hsum_bound (s : Finset Nat) :
      (∑ i ∈ s, height i) ≤ ∑ i ∈ s, (2*((height i-4)/2)+5) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact Nat.add_le_add (height_floor_bound (height a)) ih
  have h := hsum_bound (Finset.range 8)
  have hsum_identity (s : Finset Nat) :
      (∑ i ∈ s, (2*((height i-4)/2)+5)) =
        2*(∑ i ∈ s, (height i-4)/2)+5*s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      omega
  have he : (∑ i ∈ Finset.range 8, (2*((height i-4)/2)+5)) =
      2*attachmentCapacity height 4 8+40 := by
    simpa [attachmentCapacity] using hsum_identity (Finset.range 8)
  rw [he] at h
  omega

/-- Complete numeric large-parameter result. The doubled size identity and
2r≤3M+4 are the exact consequences of the manuscript's admissible parameters.
No support/occurrence hypothesis is present or concluded. -/
theorem capacity_large_numeric (μ : YoungDiagram) (M r : Nat)
    (hM : 22 ≤ M) (hr : 0 < r)
    (hsize : 2*μ.card = M*(M+1)+4*r)
    (hrange : 2*r ≤ 3*M+4)
    (hcols : 2*M-1 ≤ colPrefix μ 4)
    (hrows : 2*M-1 ≤ rowPrefix μ 4) :
    BandTest μ.colLen μ.rowLen M r ∨ BandTest μ.rowLen μ.colLen M r := by
  by_contra h
  push Not at h
  have hfcol : attachmentCapacity μ.colLen 4 8 < r := by
    by_contra hn
    apply h.1
    refine ⟨4,8,by omega,by omega,by omega,?_,by omega,by omega⟩
    exact hrows
  have hfrow : attachmentCapacity μ.rowLen 4 8 < r := by
    by_contra hn
    apply h.2
    refine ⟨4,8,by omega,by omega,by omega,?_,by omega,by omega⟩
    exact hcols
  have hc : colPrefix μ 8 ≤ 2*r+38 := prefix_eight_bound _ r hr hfcol
  have hw : rowPrefix μ 8 ≤ 2*r+38 := prefix_eight_bound _ r hr hfrow
  have hμ : 0 < μ.card := by nlinarith
  have hb := capacity_rectangle μ 8 8 (2*r+38) (2*r+38) hμ (by omega) (by omega) hc hw
  have hp : 0 ≤ (M-22)*(M-22) := Nat.zero_le _
  have hbase : 22 ≤ M := hM
  have hfirst : 2*(2*r+38) < μ.card := by nlinarith
  have hsquare : (2*r+38)*(2*r+38) < 64*μ.card := by
    have hbnd : (2*r)^2 ≤ (3*M+4)^2 := Nat.pow_le_pow_left hrange 2
    have hpoly : 1508+28*M < 23*M*M := by nlinarith
    nlinarith
  have hdiv : (2*r+38)*(2*r+38)/(8*8) < μ.card := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 8*8)).mpr
    simpa [Nat.mul_comm] using hsquare
  have hsum : (2*r+38)+(2*r+38)-1 < μ.card := by omega
  exact (not_lt_of_ge hb) (max_lt hsum hdiv)

end ArithmeticTensorSquares.Capacity

end OAI
