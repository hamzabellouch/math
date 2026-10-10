import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedReplicaWeights
import OAI.Probability.Perceptron.Variational.DepthLaw
import OAI.Probability.Perceptron.Pressure.RootPartition

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology
namespace SphericalPerceptronFreeEnergy

def CascadeShapeMatches : (n : ℕ) → (s : CascadeVisitShape n) →
    (CascadeShapeReplicas n s → IndexedLeaf n) → Prop
  | 0, _, _ => True
  | n+1, ss, xs =>
      RootPartitionMatch (fun u => (((xs u).1, (xs u).2.1), (xs u).2.2)) ∧
        ∀ i : Fin ss.length, CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2.2)

lemma indexedCommonDepth_ne_zero_iff (n : ℕ) (l m : IndexedLeaf (n+1)) :
    indexedCommonDepth (n+1) l m ≠ 0 ↔ l.1 = m.1 ∧ l.2.1 = m.2.1 := by
  simp only [indexedCommonDepth]
  split_ifs <;> simp_all

lemma cascadeShapeMatches_iff (n : ℕ) (s : CascadeVisitShape n)
    (xs : CascadeShapeReplicas n s → IndexedLeaf n) :
    CascadeShapeMatches n s xs ↔
      ∀ i j, indexedCommonDepth n (xs i) (xs j) =
        indexedCommonDepth n (cascadeShapeLeaves n s i) (cascadeShapeLeaves n s j) := by
  induction n with
  | zero => simp [CascadeShapeMatches, indexedCommonDepth]
  | succ n ih =>
    constructor
    · rintro ⟨hr, hc⟩ ⟨a,i⟩ ⟨b,j⟩
      have hroot : (xs ⟨a,i⟩).1 = (xs ⟨b,j⟩).1 ∧
          (xs ⟨a,i⟩).2.1 = (xs ⟨b,j⟩).2.1 ↔ a = b := by
        simpa only [Prod.mk.injEq] using hr ⟨a,i⟩ ⟨b,j⟩
      by_cases hab : a = b
      · subst b
        simp only [cascadeShapeLeaves, indexedCommonDepth, ite_eq_left (hroot.mpr rfl),
          and_self, ↓reduceIte]
        exact congrArg Fin.succ ((ih _ _).mp (hc a) i j)
      · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
        simp only [cascadeShapeLeaves, indexedCommonDepth, ite_eq_right (mt hroot.mp hab),
          hv, false_and, ↓reduceIte]
    · intro hm
      have hr : RootPartitionMatch (fun u => (((xs u).1, (xs u).2.1), (xs u).2.2)) := by
        intro u v
        change ((xs u).1, (xs u).2.1) = ((xs v).1, (xs v).2.1) ↔ u.1 = v.1
        rw [Prod.mk.injEq, ← indexedCommonDepth_ne_zero_iff, hm u v,
          indexedCommonDepth_ne_zero_iff]
        simp only [cascadeShapeLeaves, and_true, Fin.ext_iff]
      refine ⟨hr, fun a => (ih _ _).mpr ?_⟩
      intro i j
      have hroot : (xs ⟨a,i⟩).1 = (xs ⟨a,j⟩).1 ∧
          (xs ⟨a,i⟩).2.1 = (xs ⟨a,j⟩).2.1 := by
        simpa only [Prod.mk.injEq] using (hr ⟨a,i⟩ ⟨a,j⟩).mpr rfl
      have he := hm ⟨a,i⟩ ⟨a,j⟩
      simp only [cascadeShapeLeaves, indexedCommonDepth, ite_eq_left hroot, and_self, ↓reduceIte] at he
      exact Fin.succ_inj.mp he

def indexedActiveRootEmbedding (n : ℕ) (b : IndexedCascadeBase (n+1)) :
    (Σ i, Fin ((b i).1)) ↪ ℕ × ℕ where
  toFun a := (a.1, a.2.val)
  inj' := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    obtain ⟨hik, hjl⟩ := Prod.mk.inj he
    change i = k at hik
    subst k
    have hj : j = l := Fin.ext hjl
    subst l
    rfl

def indexedActiveLeafEmbedding (n : ℕ) (b : IndexedCascadeBase (n+1)) :
    ((Σ i, Fin ((b i).1)) × IndexedLeaf n) ↪ IndexedLeaf (n+1) where
  toFun t := (t.1.1, t.1.2.val, t.2)
  inj' := by
    intro u v he
    apply Prod.ext
    · apply (indexedActiveRootEmbedding n b).injective
      exact congrArg (fun t : IndexedLeaf (n+1) => (t.1,t.2.1)) he
    · exact congrArg (fun t : IndexedLeaf (n+1) => t.2.2) he

variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S] [Nonempty S]

def indexedShapeVisit (step : X×S → X) (n : ℕ) (F : Fin n → X×S → ℝ)
    (s : CascadeVisitShape n) (p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n)) : ℝ≥0∞ :=
  ∑' xs : CascadeShapeReplicas n s → IndexedLeaf n,
    (∏ i, indexedTiltedProbability step n F p (xs i)) *
      if CascadeShapeMatches n s xs then 1 else 0

omit [Nonempty S] in
lemma indexedShapeVisit_measurable {step : X×S → X} (hs : Measurable step)
    (n : ℕ) (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (s : CascadeVisitShape n) : Measurable (indexedShapeVisit step n F s) := by
  unfold indexedShapeVisit
  refine Measurable.tsum (fun xs => ?_)
  have hf (i : CascadeShapeReplicas n s) : Measurable
      (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) =>
        indexedTiltedProbability step n F p (xs i)) :=
    by
      have hp : Measurable (fun p : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) =>
          (p, xs i)) := measurable_id.prodMk measurable_const
      have hh := (indexedTiltedProbability_measurable (X := X) (S := S) hs n F hF).comp hp
      exact hh
  exact (Finset.measurable_prod Finset.univ (fun i _ => hf i)).mul_const _

omit [MeasurableSpace X] [Nonempty S] in
lemma indexedShapeVisit_zero (step : X×S → X) (F : Fin 0 → X×S → ℝ)
    (s : CascadeVisitShape 0) (p : X×(IndexedCascadeBase 0×IndexedCascadeMarks S 0)) :
    indexedShapeVisit step 0 F s p = 1 := by
  simp [indexedShapeVisit, CascadeShapeMatches, indexedTiltedProbability,
    indexedTiltedTotal, indexedTiltedWeight, indexedLeafWeight,
    indexedShiftSum, CascadeShapeReplicas, IndexedLeaf]

omit [MeasurableSpace X] [Nonempty S] in

lemma indexedShapeVisit_succ (step : X×S → X) (n : ℕ)
    (F : Fin (n+1) → X×S → ℝ) (ss : CascadeVisitShape (n+1))
    (hs : ss.Valid (n+1))
    (p : X×(IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1)))
    (hc : ∀ i j, 0 < (indexedTiltedTotal step n (fun l => F l.succ)
      (indexedChildPoint step n p i j)).toReal) :
    indexedShapeVisit step (n+1) F ss p =
      ∑' a : Fin ss.length ↪ (Σ i, Fin ((p.2.1 i).1)),
        ∏ i : Fin ss.length,
          (indexedBranchProbability step n F p (a i)) ^ cascadeVisitCount n ss[i] *
            indexedShapeVisit step n (fun l => F l.succ) ss[i]
              (indexedChildPoint step n p (a i).1 (a i).2.val) := by
  classical
  let J (i : Fin ss.length) := CascadeShapeReplicas n ss[i]
  let A := Σ i, Fin ((p.2.1 i).1)
  let (i : Fin ss.length) : Nonempty (J i) :=
    cascadeShapeReplicas_nonempty n ss[i] (hs.2 _ (List.getElem_mem i.isLt))
  let e := indexedActiveLeafEmbedding n p.2.1
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
  have hm (xs : (Σ i : Fin ss.length, J i) → A × IndexedLeaf n) :
      CascadeShapeMatches (n+1) ss (fun u => e (xs u)) ↔
        RootPartitionMatch xs ∧
          ∀ i : Fin ss.length, CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2) := by
    apply and_congr ?_ Iff.rfl
    constructor
    · intro h u v
      exact (indexedActiveRootEmbedding n p.2.1).injective.eq_iff.symm.trans (h u v)
    · intro h u v
      exact (indexedActiveRootEmbedding n p.2.1).injective.eq_iff.trans (h u v)
  change (∑' xs : (Σ i : Fin ss.length, J i) → IndexedLeaf (n+1),
    (∏ i, indexedTiltedProbability step (n+1) F p (xs i)) *
      if CascadeShapeMatches (n+1) ss xs then 1 else 0) = _
  rw [tsum_pi_supported e _ hw]
  calc
    _ = ∑' xs : (Σ i : Fin ss.length, J i) → A × IndexedLeaf n,
        if RootPartitionMatch xs then
          (∏ u, indexedBranchProbability step n F p (xs u).1 *
            indexedTiltedProbability step n (fun l => F l.succ)
              (indexedChildPoint step n p (xs u).1.1 (xs u).1.2.val) (xs u).2) *
          ∏ i : Fin ss.length,
            if CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2) then 1 else 0
        else 0 := by
      apply tsum_congr
      intro xs
      calc
        _ = (∏ u, indexedBranchProbability step n F p (xs u).1 *
            indexedTiltedProbability step n (fun l => F l.succ)
              (indexedChildPoint step n p (xs u).1.1 (xs u).1.2.val) (xs u).2) *
          (if RootPartitionMatch xs ∧
            ∀ i : Fin ss.length, CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2)
            then 1 else 0) := by
          exact congrArg₂ (· * ·) (Finset.prod_congr rfl (fun u _ => hweight (xs u)))
            (if_congr (hm xs) rfl rfl)
        _ = _ := by
          by_cases hr : RootPartitionMatch xs
          · simp only [hr, true_and, ↓reduceIte]
            by_cases ha : ∀ i : Fin ss.length,
                CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2)
            · simp only [ha, implies_true, ↓reduceIte, Finset.prod_const_one]
            · have hz : (∏ i : Fin ss.length,
                  if CascadeShapeMatches n ss[i] (fun j => (xs ⟨i,j⟩).2)
                  then (1 : ℝ≥0∞) else 0) = 0 := by
                obtain ⟨i, hi⟩ := not_forall.mp ha
                exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
              simp only [ha, ↓reduceIte, hz]
          · simp [hr]
    _ = _ := by
      rw [root_partition_sum_factor (J := J) (indexedBranchProbability step n F p)
        (fun a l => indexedTiltedProbability step n (fun l => F l.succ)
          (indexedChildPoint step n p a.1 a.2.val) l)
        (fun i ys => if CascadeShapeMatches n ss[i] ys then 1 else 0)]
      simp only [J, cascadeShapeReplicas_card]
      rfl

end SphericalPerceptronFreeEnergy

end

end OAI
