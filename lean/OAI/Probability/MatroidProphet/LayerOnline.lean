import OAI.Probability.MatroidProphet.Rounding
import OAI.Probability.MatroidProphet.LayerGreedy

namespace OAI

namespace MatroidProphet
open Set Finset

noncomputable def assignedEligible {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) : Finset (Fin n) := by
  classical
  exact univ.filter fun e => assign e (v e) ≠ none

def assignedLayer {n : ℕ} {K : Type*}
    (assign : Fin n → K → Option ℤ) (v : Fin n → K) (e : Fin n) : ℤ :=
  (assign e (v e)).getD 0

noncomputable def layerKeyDecision {n : ℕ} {K : Type*}
    (M : Matroid (Fin n)) (base : ℤ → Set (Fin n))
    (assign : Fin n → K → Option ℤ) (k : Fin n)
    (hist : Fin (k.val+1) → Fin n × K) : Bool := by
  classical
  let current := hist ⟨k.val, Nat.lt_succ_self _⟩
  exact match assign current.1 current.2 with
  | none => false
  | some b => decide (current.1 ∉ M.closure (base b ∪
      {f | ∃ j : Fin (k.val+1), j.val < k.val ∧ (hist j).1 = f ∧
        assign (hist j).1 (hist j).2 = some b}))

def keyHistory {n : ℕ} {K : Type*} (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) : Fin (k.val+1) → Fin n × K :=
  fun j => (π (prefixIndex k j), v (π (prefixIndex k j)))

lemma keyHistory_current {n : ℕ} {K : Type*} (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) :
    keyHistory v π k ⟨k.val, Nat.lt_succ_self _⟩ = (π k, v (π k)) := by
  rfl

lemma keyHistory_prior {n : ℕ} {K : Type*} (v : Fin n → K)
    (assign : Fin n → K → Option ℤ) (π : ArrivalOrder n) (k : Fin n) (b : ℤ) :
    {f | ∃ j : Fin (k.val+1), j.val < k.val ∧ (keyHistory v π k j).1 = f ∧
      assign (keyHistory v π k j).1 (keyHistory v π k j).2 = some b} =
    layerPrior (assignedEligible assign v) (assignedLayer assign v)
      (fun e => (π.symm e).val) b k.val := by
  classical
  ext f
  have hel : f ∈ assignedEligible assign v ∧ assignedLayer assign v f = b ↔
      assign f (v f) = some b := by
    cases h : assign f (v f) <;> simp [assignedEligible, assignedLayer, h]
  constructor
  · rintro ⟨j, hj, rfl, hb⟩
    simp only [keyHistory] at *
    refine ⟨?_, ?_, ?_⟩
    · simp [assignedEligible, hb]
    · simp [assignedLayer, hb]
    · simpa [prefixIndex] using hj
  · rintro ⟨he, hb, ht⟩
    change (π.symm f).val < k.val at ht
    have hass := hel.mp ⟨he, hb⟩
    let j : Fin (k.val+1) := ⟨(π.symm f).val, by omega⟩
    have hidx : prefixIndex k j = π.symm f := by rfl
    refine ⟨j, ht, ?_, ?_⟩
    · simp [keyHistory, hidx]
    · simpa [keyHistory, hidx] using hass

theorem layerKeyDecision_eq_greedy {n : ℕ} {K : Type*}
    (M : Matroid (Fin n)) (base : ℤ → Set (Fin n))
    (assign : Fin n → K → Option ℤ) (v : Fin n → K)
    (π : ArrivalOrder n) (k : Fin n) :
    layerKeyDecision M base assign k (keyHistory v π k) = true ↔
      π k ∈ layerGreedy M (assignedEligible assign v) base (assignedLayer assign v)
        (fun e => (π.symm e).val) := by
  classical
  unfold layerKeyDecision
  rw [keyHistory_current]
  dsimp only
  cases h : assign (π k) (v (π k)) with
  | none => simp [assignedEligible, layerGreedy, h]
  | some b =>
    dsimp only
    rw [keyHistory_prior]
    simp [layerGreedy, assignedEligible, assignedLayer, h]

noncomputable def layerOnlineRule {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ) : OnlineRule n bits :=
  discreteOnlineRule key hkey fun k r s hist =>
    layerKeyDecision M (base r s) (assign r s) k hist

theorem layerOnlineRule_accepted {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) :
    accepted (layerOnlineRule M key hkey base assign) r s v π =
      layerGreedy M (assignedEligible (assign r (fun e => key (s e))) (fun e => key (v e)))
        (base r (fun e => key (s e)))
        (assignedLayer (assign r (fun e => key (s e))) (fun e => key (v e)))
        (fun e => (π.symm e).val) := by
  classical
  ext e
  simp only [accepted, acceptedThrough, mem_filter, Finset.mem_univ, true_and,
    (π.symm e).isLt]
  change layerKeyDecision M (base r (fun e => key (s e))) (assign r (fun e => key (s e)))
    (π.symm e) (keyHistory (fun f => key (v f)) π (π.symm e)) = true ↔ _
  simpa only [Equiv.apply_symm_apply] using
    layerKeyDecision_eq_greedy M (base r (fun e => key (s e)))
      (assign r (fun e => key (s e))) (fun e => key (v e)) π (π.symm e)

lemma acceptedThrough_subset_accepted {n bits : ℕ} (A : OnlineRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough A r s v π t ⊆ accepted A r s v π := by
  classical
  intro e he
  have hd := (mem_filter.mp he).2.2
  exact mem_filter.mpr ⟨mem_univ e, (π.symm e).isLt, hd⟩

theorem layerOnlineRule_feasible {n bits : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K]
    (M : Matroid (Fin n)) (hE : M.E = Set.univ) (key : ℝ → K) (hkey : Measurable key)
    (base : Seed bits → (Fin n → K) → ℤ → Set (Fin n))
    (assign : Seed bits → (Fin n → K) → Fin n → K → Option ℤ)
    (hlower : ∀ r s v, ∀ e ∈ assignedEligible (assign r s) v,
      ∀ f ∈ assignedEligible (assign r s) v,
      assignedLayer (assign r s) v e < assignedLayer (assign r s) v f →
        e ∈ base r s (assignedLayer (assign r s) v f)) :
    Feasible M (layerOnlineRule M key hkey base assign) := by
  intro r s v π t _ _
  have htime : Function.Injective (fun e => (π.symm e).val) := by
    intro e f h
    exact π.symm.injective (Fin.ext h)
  have hi := layerGreedy_indep M
    (assignedEligible (assign r (fun e => key (s e))) (fun e => key (v e)))
    (base r (fun e => key (s e)))
    (assignedLayer (assign r (fun e => key (s e))) (fun e => key (v e)))
    (fun e => (π.symm e).val) hE htime
    (hlower r (fun e => key (s e)) (fun e => key (v e)))
  apply hi.subset
  intro e he
  have hm := acceptedThrough_subset_accepted (layerOnlineRule M key hkey base assign)
    r s v π t he
  rwa [layerOnlineRule_accepted] at hm

end MatroidProphet

end OAI
