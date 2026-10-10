import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GoodPairScores
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalGoodReference

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical
noncomputable section
variable {w r : ℕ}
def earlySlot (sel : (Fin w×Bool)→Fin r) (v : Fin w) : Slots w r :=
  Sum.inl ((v,false),sel (v,false))
def lateSlot (sel : (Fin w×Bool)→Fin r) (v : Fin w) : Slots w r :=
  Sum.inl ((v,true),sel (v,true))
def middleSlot (v : Fin w) (t : Fin (2*r)) : Slots w r := Sum.inr (v,t)
lemma early_middle_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) (t : Fin (2*r)) :
    slotEmbedding (earlySlot sel i)<slotEmbedding (middleSlot j t) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · exact representative_early _ _ _
lemma middle_late_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) (t : Fin (2*r)) :
    slotEmbedding (middleSlot i t)<slotEmbedding (lateSlot sel j) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · exact representative_late _ _ _
lemma early_late_le (sel : (Fin w×Bool)→Fin r) (i j : Fin w) (hij : i≤j) :
    slotEmbedding (earlySlot sel i)<slotEmbedding (lateSlot sel j) := by
  rcases lt_or_eq_of_le hij with h|rfl
  · exact ordered_windows _ _ h
  · simp only [earlySlot,lateSlot,Fin.lt_def,slotEmbedding_val,windowCoordinates]
    have hh:=(sel (i,false)).isLt
    omega
end
end SharpRamseyFive.Windows
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance windowScoreBlockDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance windowScoreIndexDE : DecidableEq (Slots w r) := Classical.decEq _

omit [Finite K] [Nonempty (Fin r)] in
theorem window_reference_sparse (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (J d s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i<slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : Fin w) (hij : i≤j)
    (hgood : indexBad J d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel i)=0)
    (hi : (1:ℝ)/2≤eventMass (first (map p (fun x=>x (earlySlot sel i))))
      (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s))
    (hj : (1:ℝ)/2≤eventMass (second (map p (fun x=>x (lateSlot sel j))))
      (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s)) :
    relationMass Incident
      (conditionOn (first (map p (fun x=>x (earlySlot sel i))))
        (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s) (by linarith))
      (conditionOn (second (map p (fun x=>x (lateSlot sel j))))
        (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s) (by linarith))≤320016*ε := by
  apply ordered_good_reference_sparse hdim p (slotEquiv w r) u s ε hcons _ _
    (early_late_le sel i j hij) hi hj
  exact (good_index_scores J d ε p _ (fun _ _=>orderedCollision_nonneg ..) sel _ hgood).2 (j,true)
    (by simp [OtherBlock,earlySlot])

omit [Finite K] [Nonempty (Fin r)] in
theorem window_target_right_sparse (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (J d s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i<slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : Fin w) (hij : i≤j) (t : Fin (2*r))
    (hgood : indexBad J d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot i t)=0)
    (hj : (1:ℝ)/2≤eventMass (second (map p (fun x=>x (lateSlot sel j))))
      (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s)) :
    relationMass Incident
      (fun a=>if a∈reciprocalGoodA (map p (fun x=>x (middleSlot i t))) (u (middleSlot i t)) s
        then first (map p (fun x=>x (middleSlot i t))) a else 0)
      (conditionOn (second (map p (fun x=>x (lateSlot sel j))))
        (reciprocalGoodB (map p (fun x=>x (lateSlot sel j))) (u (lateSlot sel j)) s) (by linarith))≤160008*ε := by
  rw [relationMass_restricted_conditionOn_right]
  have hh:=(ordered_reciprocal_low_conflict hdim p (slotEquiv w r) u s hcons
    (middleSlot i t) (lateSlot sel j) (middle_late_le sel i j hij t)).trans
    (mul_le_mul_of_nonneg_left
      ((good_index_scores J d ε p _ (fun _ _=>orderedCollision_nonneg ..) sel _ hgood).2 (j,true) trivial)
      (by norm_num : (0:ℝ)≤80004))
  have h:=div_half_bound _ _ _ hj (relationMass_nonneg _ _ _ (Law.nonneg _) (Law.nonneg _)) hh
  change _≤2*(80004*ε) at h
  simpa only [reciprocalGoodA,reciprocalGoodB,←mul_assoc,show (2:ℝ)*80004=160008 by norm_num] using h

omit [Finite K] [Nonempty (Fin r)] in
theorem window_target_left_sparse (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ) (sel : (Fin w×Bool)→Fin r)
    (J d s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,slotEmbedding i<slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : Fin w) (hij : i≤j) (t : Fin (2*r))
    (hgood : indexBad J d ε p (orderedCollision p (slotEquiv w r) u s) sel (middleSlot j t)=0)
    (hi : (1:ℝ)/2≤eventMass (first (map p (fun x=>x (earlySlot sel i))))
      (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s)) :
    relationMass Incident
      (conditionOn (first (map p (fun x=>x (earlySlot sel i))))
        (reciprocalGoodA (map p (fun x=>x (earlySlot sel i))) (u (earlySlot sel i)) s) (by linarith))
      (fun b=>if b∈reciprocalGoodB (map p (fun x=>x (middleSlot j t))) (u (middleSlot j t)) s
        then second (map p (fun x=>x (middleSlot j t))) b else 0)≤160008*ε := by
  rw [relationMass_conditionOn_left_restricted]
  have hh:=(ordered_reciprocal_low_conflict hdim p (slotEquiv w r) u s hcons
    (earlySlot sel i) (middleSlot j t) (early_middle_le sel i j hij t)).trans
    (mul_le_mul_of_nonneg_left
      (good_index_scores_reverse J d ε p _ (fun _ _=>orderedCollision_nonneg ..) (fun _ _=>orderedCollision_symm ..)
        sel _ hgood (i,false) trivial) (by norm_num : (0:ℝ)≤80004))
  have h:=div_half_bound _ _ _ hi (relationMass_nonneg _ _ _ (Law.nonneg _) (Law.nonneg _)) hh
  change _≤2*(80004*ε) at h
  simpa only [reciprocalGoodA,reciprocalGoodB,←mul_assoc,show (2:ℝ)*80004=160008 by norm_num] using h
end
end SharpRamseyFive.Marking

end OAI
