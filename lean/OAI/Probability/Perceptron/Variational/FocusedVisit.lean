import Mathlib
import OAI.Probability.Perceptron.Variational.PointedShape

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {X S : Type} [MeasurableSpace S]

lemma indexedClassMass_zero (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (hp : 0 < (indexedTiltedTotal step n F p).toReal) (l : IndexedLeaf n) :
    indexedClassMass step n F 0 p l = 1 := by
  simp only [indexedClassMass,Nat.zero_le,↓reduceIte,mul_one]
  exact indexedTiltedProbability_mass step n F p hp

lemma indexedFocusedVisit_zero (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (s : CascadeVisitShape n) (hs : s.Valid n)
    (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n))
    (hp : 0 < (indexedTiltedTotal step n F p).toReal) :
    indexedFocusedVisit step n F 0 s hs p = indexedShapeVisit step n F s p := by
  simp only [indexedFocusedVisit,indexedClassMass_zero step n F p hp,mul_one,indexedShapeVisit]

lemma indexedFocusedVisit_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ) (d : ℕ) (s : CascadeVisitShape n)
    (ss : List (CascadeVisitShape n)) (hs : CascadeVisitShape.Valid (n+1) (s::ss))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) :
    indexedFocusedVisit step (n+1) F (d+1) (s::ss) hs p =
      ∑' a : Fin (ss.length+1) ↪ (Σ i, Fin ((p.2.1 i).1)),
        (indexedBranchProbability step n F p (a 0)) ^ (cascadeVisitCount n s+1) *
          indexedFocusedVisit step n (fun l => F l.succ) d s (hs.2 s (by simp))
            (indexedChildPoint step n p (a 0).1 (a 0).2.val) *
        ∏ i : Fin ss.length,
          (indexedBranchProbability step n F p (a i.succ)) ^ cascadeVisitCount n ss[i] *
            indexedShapeVisit step n (fun l => F l.succ) ss[i]
              (indexedChildPoint step n p (a i.succ).1 (a i.succ).2.val) := by
  let ts : CascadeVisitShape (n+1) := s::ss
  let J (i : Fin (ss.length+1)) := CascadeShapeReplicas n ts[i]
  let A := Σ i, Fin ((p.2.1 i).1)
  let (i : Fin (ss.length+1)) : Nonempty (J i) :=
    cascadeShapeReplicas_nonempty n ts[i] (hs.2 _ (List.getElem_mem i.isLt))
  let e := indexedActiveLeafEmbedding n p.2.1
  let r : J 0 := cascadeShapeFocus n s (hs.2 s (by simp))
  have hw (l : IndexedLeaf (n+1)) (hl : l ∉ Set.range e) :
      indexedTiltedProbability step (n+1) F p l = 0 := by
    apply indexedTiltedProbability_inactive
    intro h
    exact hl ⟨(⟨l.1, ⟨l.2.1,h⟩⟩,l.2.2), rfl⟩
  have hweight (t : A × IndexedLeaf n) :
      indexedTiltedProbability step (n+1) F p (e t) =
        indexedBranchProbability step n F p t.1 *
          indexedTiltedProbability step n (fun l => F l.succ)
            (indexedChildPoint step n p t.1.1 t.1.2.val) t.2 :=
    indexedTiltedProbability_active step n F p t.1 (hc _ _) t.2
  have hm (xs : (Σ i : Fin (ss.length+1), J i) → A × IndexedLeaf n) :
      CascadeShapeMatches (n+1) ts (fun u => e (xs u)) ↔
        RootPartitionMatch xs ∧
          ∀ i : Fin (ss.length+1), CascadeShapeMatches n ts[i] (fun j => (xs ⟨i,j⟩).2) := by
    apply and_congr ?_ Iff.rfl
    constructor
    · intro h u v
      exact (indexedActiveRootEmbedding n p.2.1).injective.eq_iff.symm.trans (h u v)
    · intro h u v
      exact (indexedActiveRootEmbedding n p.2.1).injective.eq_iff.trans (h u v)
  change (∑' xs : (Σ i : Fin (ss.length+1), J i) → IndexedLeaf (n+1),
    ((∏ i, indexedTiltedProbability step (n+1) F p (xs i)) *
      if CascadeShapeMatches (n+1) ts xs then 1 else 0) *
        indexedClassMass step (n+1) F (d+1) p (xs ⟨0,r⟩)) = _
  simp_rw [mul_assoc]
  rw [tsum_pi_supported e _ hw]
  calc
    _ = ∑' xs : (Σ i : Fin (ss.length+1), J i) → A × IndexedLeaf n,
      if RootPartitionMatch xs then
        ((∏ u, indexedBranchProbability step n F p (xs u).1 *
          indexedTiltedProbability step n (fun l => F l.succ)
            (indexedChildPoint step n p (xs u).1.1 (xs u).1.2.val) (xs u).2) *
          ∏ i : Fin (ss.length+1),
            if CascadeShapeMatches n ts[i] (fun j => (xs ⟨i,j⟩).2) then 1 else 0) *
          (indexedBranchProbability step n F p (xs ⟨0,r⟩).1 *
            indexedClassMass step n (fun l => F l.succ) d
              (indexedChildPoint step n p (xs ⟨0,r⟩).1.1 (xs ⟨0,r⟩).1.2.val) (xs ⟨0,r⟩).2)
      else 0 := by
      apply tsum_congr
      intro xs
      have hprod := Finset.prod_congr rfl (fun u (_ : u ∈ Finset.univ) => hweight (xs u))
      have hind := if_congr (hm xs) (rfl : (1:ℝ≥0∞)=1) (rfl : (0:ℝ≥0∞)=0)
      have hmass := indexedClassMass_active_succ step n F d p hc (xs ⟨0,r⟩).1 (xs ⟨0,r⟩).2
      change _ = _ at hmass
      calc
        _ = ((∏ u, indexedBranchProbability step n F p (xs u).1 *
          indexedTiltedProbability step n (fun l => F l.succ)
            (indexedChildPoint step n p (xs u).1.1 (xs u).1.2.val) (xs u).2) *
          (if RootPartitionMatch xs ∧ ∀ i : Fin (ss.length+1),
            CascadeShapeMatches n ts[i] (fun j => (xs ⟨i,j⟩).2) then 1 else 0)) *
          (indexedBranchProbability step n F p (xs ⟨0,r⟩).1 *
            indexedClassMass step n (fun l => F l.succ) d
              (indexedChildPoint step n p (xs ⟨0,r⟩).1.1 (xs ⟨0,r⟩).1.2.val) (xs ⟨0,r⟩).2) := by
          rw [← mul_assoc]
          exact congrArg₂ (· * ·) (congrArg₂ (· * ·) hprod hind) hmass
        _ = _ := by
          by_cases hr : RootPartitionMatch xs
          · simp only [hr,true_and,↓reduceIte]
            by_cases ha : ∀ i : Fin (ss.length+1),
                CascadeShapeMatches n ts[i] (fun j => (xs ⟨i,j⟩).2)
            · simp only [ha, implies_true, ↓reduceIte, Finset.prod_const_one]
            · have hz : (∏ i : Fin (ss.length+1),
                  if CascadeShapeMatches n ts[i] (fun j => (xs ⟨i,j⟩).2)
                  then (1 : ℝ≥0∞) else 0) = 0 := by
                obtain ⟨i, hi⟩ := not_forall.mp ha
                exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
              simp only [ha, ↓reduceIte, hz]
          · simp [hr]
    _ = _ := by
      rw [root_partition_sum_focused ss.length J r (indexedBranchProbability step n F p)
        (fun a l => indexedTiltedProbability step n (fun l => F l.succ)
          (indexedChildPoint step n p a.1 a.2.val) l)
        (fun i ys => if CascadeShapeMatches n ts[i] ys then 1 else 0)
        (fun a ys => indexedClassMass step n (fun l => F l.succ) d
          (indexedChildPoint step n p a.1 a.2.val) (ys r))]
      simp only [J,cascadeShapeReplicas_card,ts]
      simp only [indexedFocusedVisit,indexedShapeVisit,mul_assoc]
      rfl

end SphericalPerceptronFreeEnergy

end

end OAI
