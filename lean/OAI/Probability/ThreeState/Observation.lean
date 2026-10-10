import Mathlib
import OAI.Probability.ThreeState.Messages

namespace OAI

/-! Ordered and unlabelled boundary observations and information degradation. -/

namespace ThreeState

 

noncomputable def iidVector {α : Type*} (p : PMF α) : (n : ℕ) → PMF (Fin n → α)
  | 0 => PMF.pure Fin.elim0
  | n+1 => p.bind (fun a => (iidVector p n).map (Fin.cons a))

lemma iidVector_map {α β : Type*} (p : PMF α) (f : α → β) (n : ℕ) :
    (iidVector p n).map (fun as => f ∘ as) = iidVector (p.map f) n := by
  induction n with
  | zero =>
    simp only [iidVector, PMF.pure_map]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [iidVector, PMF.map_bind, PMF.map_comp, PMF.bind_map]
    apply congrArg (PMF.bind p)
    funext a
    rw [← ih]
    dsimp only [Function.comp_def]
    rw [PMF.map_comp]
    congr 1
    funext v j
    cases j using Fin.cases <;> simp

lemma iidVector_ofFn {α : Type*} (p : PMF α) (n : ℕ) :
    (iidVector p n).map List.ofFn = iidList p n := by
  induction n with
  | zero => simp [iidVector, iidList, PMF.pure_map]
  | succ n ih =>
    simp only [iidVector, iidList, PMF.map_bind, PMF.map_comp]
    apply congrArg (PMF.bind p)
    funext a
    rw [← ih, PMF.map_comp]
    congr 1
    funext v
    simp [List.ofFn_succ]

lemma iidVector_apply {α : Type*} (p : PMF α) (n : ℕ) (v : Fin n → α) :
    iidVector p n v = ∏ j, p (v j) := by
  classical
  induction n with
  | zero =>
    have he : v = Fin.elim0 := by funext j; exact Fin.elim0 j
    simp [iidVector, he]
  | succ n ih =>
    simp only [iidVector, PMF.bind_apply, PMF.map_apply]
    have he (a : α) (w : Fin n → α) : (v = Fin.cons a w) ↔ (a=v 0 ∧ w=Fin.tail v) := by
      constructor
      · intro h
        subst v
        simp
      · rintro ⟨rfl,rfl⟩
        exact (Fin.cons_self_tail v).symm
    simp_rw [he]
    simp only [ite_and]
    rw [tsum_eq_single (v 0)]
    · simp [ih, Fin.prod_univ_succ, Fin.tail]
    · intro a ha
      simp [ha]

 
abbrev OrderedObservation : ℕ → Type
  | 0 => Spin
  | n+1 => Σ k : ℕ, Fin k → OrderedObservation n

noncomputable def orderedLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Spin → PMF (OrderedObservation n)
  | 0, i => PMF.pure i
  | n+1, i => offspring.bind (fun k =>
      (iidVector ((channelPMF lam h i).bind (orderedLaw offspring lam h n)) k).map (Sigma.mk k))

def forgetOrder : (n : ℕ) → OrderedObservation n → Observation n
  | 0, i => i
  | n+1, ⟨k,v⟩ => (List.ofFn (fun j : Fin k => forgetOrder n (v j)) : Multiset (Observation n))

lemma orderedLaw_forget (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (orderedLaw offspring lam h n i).map (forgetOrder n) = observedLaw offspring lam h n i := by
  induction n generalizing i with
  | zero =>
    change (PMF.pure i).map id = PMF.pure i
    exact PMF.map_id _
  | succ n ih =>
    simp only [orderedLaw, observedLaw, PMF.map_bind, PMF.map_comp]
    apply congrArg (PMF.bind offspring)
    funext k
    let p := (channelPMF lam h i).bind (orderedLaw offspring lam h n)
    change (iidVector p k).map
      ((fun xs : List (Observation n) => (xs : Multiset (Observation n))) ∘ List.ofFn ∘
        (fun v => forgetOrder n ∘ v)) = _
    rw [← PMF.map_comp, ← PMF.map_comp, iidVector_map, iidVector_ofFn]
    congr 2
    rw [PMF.map_bind]
    congr 1
    funext j
    exact ih j

lemma orderedAdvantage_dominates (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) :
    advantage (observedLaw offspring lam h n) ≤ advantage (orderedLaw offspring lam h n) := by
  have hh := advantage_bind_le (orderedLaw offspring lam h n) (fun y => PMF.pure (forgetOrder n y))
  have he : (fun i => (orderedLaw offspring lam h n i).bind (fun y => PMF.pure (forgetOrder n y))) =
      observedLaw offspring lam h n := by
    funext i
    exact orderedLaw_forget offspring lam h n i
  rw [he] at hh
  exact hh

end ThreeState

namespace ThreeState

noncomputable def vectorTraverse {α β : Type*} (k : α → PMF β) :
    (n : ℕ) → (Fin n → α) → PMF (Fin n → β)
  | 0, _ => PMF.pure Fin.elim0
  | n+1, v => (k (v 0)).bind (fun b => (vectorTraverse k n (Fin.tail v)).map (Fin.cons b))

lemma vectorTraverse_cons {α β : Type*} (k : α → PMF β) (n : ℕ) (a : α) (v : Fin n → α) :
    vectorTraverse k (n+1) (Fin.cons a v) =
      (k a).bind (fun b => (vectorTraverse k n v).map (Fin.cons b)) := by
  simp only [vectorTraverse, Fin.cons_zero, Fin.tail_cons]

lemma iidVector_bind_traverse {α β : Type*} (p : PMF α) (k : α → PMF β) (n : ℕ) :
    (iidVector p n).bind (vectorTraverse k n) = iidVector (p.bind k) n := by
  induction n with
  | zero => simp only [iidVector, PMF.pure_bind, vectorTraverse]
  | succ n ih =>
    simp only [iidVector, PMF.bind_bind, PMF.bind_map, Function.comp_def, vectorTraverse_cons]
    apply congrArg (PMF.bind p)
    funext a
    rw [PMF.bind_comm]
    apply congrArg (PMF.bind (k a))
    funext b
    rw [← PMF.map_bind, ih]

noncomputable def orderedGrow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → OrderedObservation n → PMF (OrderedObservation (n+1))
  | 0 => orderedLaw offspring lam h 1
  | n+1 => fun ⟨k,v⟩ => (vectorTraverse (orderedGrow offspring lam h n) k v).map (Sigma.mk k)

lemma orderedLaw_grow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (orderedLaw offspring lam h n i).bind (orderedGrow offspring lam h n) =
      orderedLaw offspring lam h (n+1) i := by
  induction n generalizing i with
  | zero => exact PMF.pure_bind i _
  | succ n ih =>
    simp only [orderedLaw, orderedGrow, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply congrArg (PMF.bind offspring)
    funext k
    rw [← PMF.map_bind, iidVector_bind_traverse, PMF.bind_bind]
    have he : (fun j => (orderedLaw offspring lam h n j).bind (orderedGrow offspring lam h n)) =
        orderedLaw offspring lam h (n+1) := funext ih
    rw [he]
    rfl

lemma ordered_likelihood_common_subsequence (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    ∃ Q : MeasureTheory.ProbabilityMeasure Message, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => likelihoodLaw (orderedLaw offspring lam h (φ n))) Filter.atTop (nhds Q) ∧
      Filter.Tendsto (fun n => likelihoodLaw (orderedLaw offspring lam h (φ n+1))) Filter.atTop (nhds Q) := by
  exact likelihood_common_subsequence (orderedLaw offspring lam h) (orderedGrow offspring lam h)
    (fun n i => (orderedLaw_grow offspring lam h n i).symm)

end ThreeState
universe u
namespace ThreeState

instance pmfCommApplicative : CommApplicative PMF where
  commutative_prod a b := by
    change ((a.map Prod.mk).bind (fun f => b.map f)) =
      ((b.map (fun y x => (x,y))).bind (fun f => a.map f))
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    exact PMF.bind_comm a b (fun x y => PMF.pure (x,y))

lemma list_traverse_nil {α β : Type u} (k : α → PMF β) :
    Traversable.traverse k [] = PMF.pure [] := rfl

lemma list_traverse_cons {α β : Type u} (k : α → PMF β) (a : α) (as : List α) :
    Traversable.traverse k (a::as) = (k a).bind (fun b => (Traversable.traverse k as).map (List.cons b)) := by
  rw [List.traverse_cons, seq_eq_bind_map]
  change ((k a).map List.cons).bind _ = _
  rw [PMF.bind_map]
  rfl

lemma multiset_traverse_list {α β : Type u} (k : α → PMF β) (as : List α) :
    Multiset.traverse k (as : Multiset α) =
      (Traversable.traverse k as).map (fun bs : List β => (bs : Multiset β)) := rfl

lemma iidList_bind_traverse {α β : Type u} (p : PMF α) (k : α → PMF β) (n : ℕ) :
    (iidList p n).bind (Traversable.traverse k) = iidList (p.bind k) n := by
  induction n with
  | zero => simp only [iidList, PMF.pure_bind, list_traverse_nil]
  | succ n ih =>
    simp only [iidList, PMF.bind_bind, PMF.bind_map, Function.comp_def, list_traverse_cons]
    apply congrArg (PMF.bind p)
    funext a
    rw [PMF.bind_comm]
    apply congrArg (PMF.bind (k a))
    funext b
    rw [← PMF.map_bind, ih]

lemma iidList_multiset_bind {α β : Type u} (p : PMF α) (k : α → PMF β) (n : ℕ) :
    ((iidList p n).map (fun as : List α => (as : Multiset α))).bind (Multiset.traverse k) =
      (iidList (p.bind k) n).map (fun bs : List β => (bs : Multiset β)) := by
  rw [PMF.bind_map]
  change (iidList p n).bind (fun as => ((Traversable.traverse k as).map (fun bs : List β => (bs : Multiset β)))) = _
  rw [← PMF.map_bind, iidList_bind_traverse]

 

noncomputable def grow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Observation n → PMF (Observation (n+1))
  | 0 => observedLaw offspring lam h 1
  | n+1 => Multiset.traverse (grow offspring lam h n)

 
theorem observedLaw_grow (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (observedLaw offspring lam h n i).bind (grow offspring lam h n) =
      observedLaw offspring lam h (n+1) i := by
  induction n generalizing i with
  | zero => exact PMF.pure_bind i _
  | succ n ih =>
    change (offspring.bind (fun k =>
      (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h n)) k).map
        (fun xs : List (Observation n) => (xs : Multiset (Observation n))))).bind
        (Multiset.traverse (grow offspring lam h n)) =
      offspring.bind (fun k =>
        (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h (n+1))) k).map
          (fun xs : List (Observation (n+1)) => (xs : Multiset (Observation (n+1)))))
    rw [PMF.bind_bind]
    apply congrArg (PMF.bind offspring)
    funext k
    rw [iidList_multiset_bind, PMF.bind_bind]
    have he : (fun j => (observedLaw offspring lam h n j).bind (grow offspring lam h n)) =
        observedLaw offspring lam h (n+1) := funext ih
    rw [he]

 
theorem observedAdvantage_antitone (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    Antitone (fun n => advantage (observedLaw offspring lam h n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have he : observedLaw offspring lam h (n+1) =
      fun i => (observedLaw offspring lam h n i).bind (grow offspring lam h n) := by
    funext i
    exact (observedLaw_grow offspring lam h n i).symm
  rw [he]
  exact advantage_bind_le _ _

 
theorem observedAdvantage_tendsto (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ 1 ∧
      Filter.Tendsto (fun n => advantage (observedLaw offspring lam h n))
        Filter.atTop (nhds L) := by
  let a := fun n => advantage (observedLaw offspring lam h n)
  have hb : BddBelow (Set.range a) := ⟨0, by rintro x ⟨n,rfl⟩; exact advantage_nonneg _⟩
  refine ⟨⨅ n, a n, ?_, ?_, tendsto_atTop_ciInf (observedAdvantage_antitone offspring lam h) hb⟩
  · exact le_ciInf (fun n => advantage_nonneg _)
  · exact (ciInf_le hb 0).trans (advantage_le_one _)

end ThreeState

end OAI
