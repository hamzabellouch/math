import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScalarCells

namespace OAI

/-! # Retaining a prepared state across one bounded scalar stage -/

namespace LowSpaceSubsetSum.ScalarStageCells

theorem bound (n u C k P X : ℕ) (hu : n+2 ≤ u) (hu0 : 10000 ≤ u) (hk : 5 ≤ k)
    (hP : P ≤ u^k*(C+1)) (hX : X ≤ 9*n^3+320) :
    P+X+9*n^3+512 ≤ u^(k+1)*(C+1) := by
  have h3 := Nat.pow_le_pow_left (show n ≤ u by omega) 3
  have h3p : 1 ≤ u^3 := Nat.one_le_pow _ _ (by omega)
  have hsmall : X+9*n^3+512 ≤ u^5 := by
    have hcoef : 850 ≤ u^2 := by nlinarith only [hu0]
    have hm := Nat.mul_le_mul_right (u^3) hcoef
    rw [← pow_add] at hm
    change 850*u^3 ≤ u^5 at hm
    nlinarith only [hX, h3, h3p, hm]
  have hminor := hsmall.trans ((pow_le_pow_right' (by omega : 1 ≤ u) hk).trans
    (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1)))
  have hf : 2*u^k ≤ u^(k+1) := by
    calc
      _ ≤ u*u^k := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hm := Nat.mul_le_mul_right (C+1) hf
  simp only [Nat.mul_assoc] at hm
  omega

/-- Three scalar stages together add only polynomial seed and scratch cells. -/
theorem aggregate (n u C P Q : ℕ) (hu : n+2 ≤ u) (hu0 : 10000 ≤ u)
    (hP : P ≤ u^12*(C+1)) (hQ : Q ≤ 48*n^3+2240) :
    P+Q ≤ u^13*(C+1) := by
  have h3 := Nat.pow_le_pow_left (show n ≤ u by omega) 3
  have h3p : 1 ≤ u^3 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_right (u^3) (show 2288 ≤ u by omega)
  have hq : Q ≤ u^4 := by
    rw [← pow_succ'] at hm
    change 2288*u^3 ≤ u^4 at hm
    nlinarith only [hQ, h3, h3p, hm]
  have h412 : u^4 ≤ u^12 := pow_le_pow_right' (by omega) (by decide)
  have hminor := hq.trans (h412.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1)))
  have hf : 2*u^12 ≤ u^13 := by
    calc
      _ ≤ u*u^12 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right (C+1) hf
  simp only [Nat.mul_assoc] at hfinal
  omega

end LowSpaceSubsetSum.ScalarStageCells

end OAI
