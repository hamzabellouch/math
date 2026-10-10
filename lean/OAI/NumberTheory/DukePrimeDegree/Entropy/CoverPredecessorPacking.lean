import OAI.NumberTheory.DukePrimeDegree.Geometry.FirstCoverLocalPacking
import OAI.NumberTheory.DukePrimeDegree.Geometry.ScaledMatrixBalls

namespace OAI

/-! # Bounding predecessor covering labels after one diagonal step

A single small image cell pulls back to a uniformly small chart. The
separated-cover packing bound then controls its possible source labels.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

def predecessorPackingRadius (n : ℕ) (a : G n) (C D : ℝ) : ℝ :=
  let A := 2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C
  ((n:ℝ)*A)*((n:ℝ)*D)+(n:ℝ)*A+(n:ℝ)*D+1

theorem firstCover_predecessor_label_bound {n N : ℕ} (hn : 0 < n)
    (z : Fin N → X n) (c : Fin N → ℝ) (E : Set (X n)) (x : X n)
    (a : G n) {C D δ : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*predecessorPackingRadius n a C D*δ ≤ 1/2)
    (hsep : ∀ i j, i ≠ j → δ ≤ quotientLogDistance (z i) (z j))
    (hcover : ∀ y ∈ E, ∃ i, quotientLogDistance (z i) y < c i)
    (himage : ∀ y ∈ E, ∃ p ∈ matrixBall n (C*δ),
      rightAction (rightAction x a) p=rightAction y a)
    (hcell : ∀ i y, y ∈ E → quotientLogDistance (z i) y < c i →
      ∃ h ∈ matrixBall n (D*δ), rightAction y h=z i) :
    ∃ F : Finset (Fin (N+1)),
      (firstCoverCode (fun i => quotientLogDistance (z i)) c) '' E ⊆ F ∧
        (F.card:ℝ) ≤ localQuotientPackingBound n (predecessorPackingRadius n a C D) := by
  let A := 2*(n:ℝ)*Real.exp (2*matrixLogLength a)*C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ predecessorPackingRadius n a C D := by
    dsimp [predecessorPackingRadius]
    positivity
  apply firstCover_local_label_bound_of_lifts hn z c E x hK hδ hδ1 hsmall hsep hcover
  intro i hi
  obtain ⟨y,hy,hiy⟩ := hi
  obtain ⟨p,hp,hpa⟩ := himage y hy
  obtain ⟨h,hh,hyh⟩ := hcell i y hy hiy
  let q := a*p*a⁻¹
  have hq : q ∈ matrixBall n (A*δ) := by
    simpa only [inv_inv,matrixLogLength_inv,A,q] using
      matrixBall_right_translate_scaled hn a⁻¹ hC hδ hp
  have hxq : rightAction x q=y := by
    calc
      _ = rightAction (rightAction (rightAction x a) p) a⁻¹ := by
        change rightAction x (a*p*a⁻¹)=_
        simp only [rightAction_mul,mul_assoc]
      _ = rightAction (rightAction y a) a⁻¹ := by rw [hpa]
      _ = y := by rw [rightAction_mul,mul_inv_cancel,rightAction_one]
  refine ⟨q*h,?_,?_⟩
  · exact matrixBall_mul_scaled hA hD hδ hδ1 hq hh
  · rw [←rightAction_mul,hxq,hyh]

end DukePrimeDegree

end

end OAI
