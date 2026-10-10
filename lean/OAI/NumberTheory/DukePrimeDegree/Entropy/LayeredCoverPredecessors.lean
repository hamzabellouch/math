import OAI.NumberTheory.DukePrimeDegree.Entropy.CoverPredecessorPacking
import OAI.NumberTheory.DukePrimeDegree.Entropy.LayeredPredecessors

namespace OAI

/-! # Finite predecessor counts for geometric layered covers -/

noncomputable section
open Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem layered_cover_uniform_predecessors {n : ℕ} (hn : 0 < n)
    (a : G n) (H : X n → ℕ) (N : ℕ → ℕ)
    (z : ∀ k, Fin (N k) → X n) (c : ∀ k, Fin (N k) → ℝ)
    (r δ : ℕ → ℝ) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (hδ : ∀ k, 0 < δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hsmall : ∀ k, (n:ℝ)*predecessorPackingRadius n a C D*δ k ≤ 1/2)
    (hstep : ∀ x, H (rightAction x a) ≤ H x+1 ∧ H x ≤ H (rightAction x a)+1)
    (hsource : ∀ k, r k ≤ D*δ k)
    (himage : ∀ x, r (H (rightAction x a)) ≤ C*δ (H x))
    (hsep : ∀ k i j, i ≠ j → δ k ≤ quotientLogDistance (z k i) (z k j))
    (hcut : ∀ k i, 0 < c k i)
    (hcover : ∀ k x, H x=k → ∃ i, quotientLogDistance (z k i) x<c k i)
    (hcell : ∀ k i x, quotientLogDistance (z k i) x<c k i →
      ∀ y, quotientLogDistance (z k i) y<c k i →
      ∃ g ∈ matrixBall n (r k), rightAction x g=y) :
    UniformFinitePredecessors (fun x => rightAction x a)
      (layeredObservation H (fun k => firstCoverCode (fun i => quotientLogDistance (z k i)) (c k))) := by
  classical
  let P := fun k => firstCoverCode (fun i => quotientLogDistance (z k i)) (c k)
  let Q := layeredObservation H P
  obtain ⟨M,hM⟩ := exists_nat_gt (localQuotientPackingBound n (predecessorPackingRadius n a C D))
  apply uniformFinitePredecessors_of_height_layers _ H Q hstep
    (fun _ _ he => (layeredObservation_eq H P he).1) M
  intro q k
  let E := {y : X n | H y=k ∧ Q (rightAction y a)=q}
  by_cases he : E.Nonempty
  · obtain ⟨x,hx⟩ := he
    have himg : ∀ y ∈ E, ∃ p ∈ matrixBall n (C*δ k),
        rightAction (rightAction x a) p=rightAction y a := by
      intro y hy
      have heq : P (H (rightAction x a)) (rightAction y a)=
          P (H (rightAction x a)) (rightAction x a) :=
        (layeredObservation_eq H P (hy.2.trans hx.2.symm)).2
      obtain ⟨i,hyi,hxi⟩ := firstCoverCode_common
        (fun i => quotientLogDistance (z (H (rightAction x a)) i))
        (c (H (rightAction x a))) (hcover _ _ rfl) heq
      obtain ⟨g,hg,hgy⟩ := hcell _ i _ hxi _ hyi
      refine ⟨g,matrixBall_mono ?_ hg,hgy⟩
      simpa only [hx.1] using himage x
    have hctr : ∀ i y, y ∈ E → quotientLogDistance (z k i) y<c k i →
        ∃ h ∈ matrixBall n (D*δ k), rightAction y h=z k i := by
      intro i y _ hiy
      obtain ⟨g,hg,hgz⟩ := hcell k i y hiy (z k i) (by
        simpa only [quotientLogDistance_self] using hcut k i)
      exact ⟨g,matrixBall_mono (hsource k) hg,hgz⟩
    obtain ⟨F,hF,hcard⟩ := firstCover_predecessor_label_bound hn (z k) (c k) E x a
      hC hD (hδ k) (hδ1 k) (hsmall k) (hsep k)
      (fun y hy => hcover k y hy.1) himg hctr
    refine ⟨F.image (fun u => Nat.pair k u.val),?_,?_⟩
    · rintro _ ⟨y,hy,rfl⟩
      have hyP : P k y ∈ F := hF ⟨y,hy,rfl⟩
      apply Finset.mem_image.mpr
      refine ⟨P k y,hyP,?_⟩
      change Nat.pair k (P k y).val=Nat.pair (H y) (P (H y) y).val
      rw [hy.1]
    · have hc : F.card ≤ M := by exact_mod_cast (hcard.trans hM.le)
      exact (Finset.card_image_le).trans hc
  · refine ⟨∅,?_,by simp⟩
    rintro _ ⟨y,hy,_⟩
    exact (he ⟨y,hy⟩).elim

end DukePrimeDegree

end

end OAI
