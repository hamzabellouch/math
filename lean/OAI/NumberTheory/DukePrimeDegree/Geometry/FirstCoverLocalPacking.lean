import OAI.NumberTheory.DukePrimeDegree.Geometry.FirstCoverCode
import OAI.NumberTheory.DukePrimeDegree.Geometry.LocalQuotientPacking

namespace OAI

/-! # Local bounds for the actual first-cover labels

If the covering balls meeting a set have their separated centers in one
small relative chart, only uniformly many of the actual labels occur.
-/

noncomputable section
open Set MeasureTheory
namespace DukePrimeDegree
open PrimeDegreePackets

theorem firstCover_local_label_bound_of_lifts {n N : ℕ} (hn : 0 < n)
    (z : Fin N → X n) (c : Fin N → ℝ) (E : Set (X n)) (x : X n)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hsep : ∀ i j, i ≠ j → δ ≤ quotientLogDistance (z i) (z j))
    (hcover : ∀ y ∈ E, ∃ i, quotientLogDistance (z i) y < c i)
    (hnear : ∀ i, (∃ y ∈ E, quotientLogDistance (z i) y < c i) →
      ∃ g ∈ matrixBall n (C*δ), rightAction x g=z i) :
    ∃ F : Finset (Fin (N+1)),
      (firstCoverCode (fun i => quotientLogDistance (z i)) c) '' E ⊆ F ∧
        (F.card:ℝ) ≤ localQuotientPackingBound n C := by
  classical
  let I : Finset (Fin N) := Finset.univ.filter
    (fun i => ∃ y ∈ E, quotientLogDistance (z i) y < c i)
  let f : Fin N → Fin (N+1) := fun i => ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩
  have hbound : (I.card:ℝ) ≤ localQuotientPackingBound n C := by
    apply local_quotient_packing_finset_bound hn I z x hC hδ hδ1 hsmall
    · intro i hi
      exact hnear i (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact hsep i j hij
  refine ⟨I.image f,?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨i,hi,hiy⟩ := firstCoverCode_selected
      (fun i => quotientLogDistance (z i)) c y (hcover y hy)
    have hiI : i ∈ I := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,y,hy,hiy⟩
    apply Finset.mem_image.mpr
    refine ⟨i,hiI,?_⟩
    exact Fin.ext hi.symm
  · exact (show ((I.image f).card:ℝ) ≤ I.card by
      exact_mod_cast Finset.card_image_le).trans hbound

theorem firstCover_local_label_bound {n N : ℕ} (hn : 0 < n)
    (z : Fin N → X n) (c : Fin N → ℝ) (E : Set (X n)) (x : X n)
    {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : (n:ℝ)*C*δ ≤ 1/2)
    (hsep : ∀ i j, i ≠ j → δ ≤ quotientLogDistance (z i) (z j))
    (hcover : ∀ y ∈ E, ∃ i, quotientLogDistance (z i) y < c i)
    (hnear : ∀ i, (∃ y ∈ E, quotientLogDistance (z i) y < c i) →
      quotientLogDistance x (z i) < Real.log (1+C*δ)) :
    ∃ F : Finset (Fin (N+1)),
      (firstCoverCode (fun i => quotientLogDistance (z i)) c) '' E ⊆ F ∧
        (F.card:ℝ) ≤ localQuotientPackingBound n C := by
  apply firstCover_local_label_bound_of_lifts hn z c E x hC.le hδ hδ1 hsmall hsep hcover
  intro i hi
  exact exists_matrix_lift_of_logDistance_lt (mul_pos hC hδ) (hnear i hi)

end DukePrimeDegree

end

end OAI
