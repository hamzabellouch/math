import OAI.Probability.MatroidProphet.Main
import Mathlib.Combinatorics.Matroid.Map

namespace OAI

namespace MatroidProphet.LabeledTransport

open MeasureTheory Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {n bits : ℕ}

/-- The same offline maximum on an arbitrary finite label type. -/
noncomputable def optimum (M : Matroid α) (w : α → ℝ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun I : Finset α => if M.Indep (I : Set α) then ∑ a ∈ I, w a else 0)

theorem sum_le_optimum (M : Matroid α) (w : α → ℝ) (I : Finset α)
    (hI : M.Indep (I : Set α)) : (∑ a ∈ I, w a) ≤ optimum M w := by
  classical
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Finset α)))
    (f := fun J => if M.Indep (J : Set α) then ∑ a ∈ J, w a else 0)
    (Finset.mem_univ I)
  simpa only [optimum, ite_eq_left hI] using h

theorem optimum_nonneg (M : Matroid α) (w : α → ℝ) : 0 ≤ optimum M w := by
  simpa using sum_le_optimum M w ∅ (by simp)

omit [Fintype α] in
/-- Relabeling preserves the full ground set; it does not discard loops. -/
theorem mapEquiv_ground (M : Matroid α) (hE : M.E = Set.univ)
    (e : α ≃ Fin n) : (M.mapEquiv e).E = Set.univ := by
  simp [hE]

/-- The all-independent-sets benchmark is exactly unchanged by label encoding. -/
theorem optimum_eq_indexed (M : Matroid α) (e : α ≃ Fin n) (w : α → ℝ) :
    optimum M w = MatroidProphet.optimum (M.mapEquiv e) (w ∘ e.symm) := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro I _
    split_ifs with hI
    · have hi : (M.mapEquiv e).Indep ((I.map e.toEmbedding : Finset (Fin n)) : Set (Fin n)) := by
        simpa using hI.map e e.injective.injOn
      have h := MatroidProphet.sum_le_optimum (M.mapEquiv e) (w ∘ e.symm)
        (I.map e.toEmbedding) hi
      simpa using h
    · exact MatroidProphet.optimum_nonneg _ _
  · apply Finset.sup'_le
    intro I _
    split_ifs with hI
    · have hi : M.Indep ((I.map e.symm.toEmbedding : Finset α) : Set α) := by
        simpa using (Matroid.mapEquiv_indep_iff.mp hI)
      have h := sum_le_optimum M w (I.map e.symm.toEmbedding) hi
      simpa using h
    · exact optimum_nonneg _ _

abbrev History (α : Type*) {n : ℕ} (k : Fin n) := Fin (k.val + 1) → α × ℝ

/-- A physical arrival order visits every label once, indexed by arrival time. -/
abbrev ArrivalOrder (α : Type*) (n : ℕ) := Fin n ≃ α

instance arrivalOrderMeasurableSpace : MeasurableSpace (ArrivalOrder α n) := ⊤

instance arrivalOrderMeasurableSingletonClass :
    MeasurableSingletonClass (ArrivalOrder α n) := ⟨fun _ => trivial⟩

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- A rule on physical labels receives only the same sample and history data. -/
structure OnlineRule (α : Type*) [MeasurableSpace α] (n bits : ℕ) where
  decide : (k : Fin n) → Seed bits → (α → ℝ) → History α k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : Seed bits × ((α → ℝ) × History α k) => decide k x.1 x.2.1 x.2.2)

def encodeHistory (e : α ≃ Fin n) {k : Fin n} (h : History α k) :
    MatroidProphet.History n k := fun j => (e (h j).1, (h j).2)

/-- Decode the indexed rule without adding any future-information input. -/
noncomputable def decodeRule (e : α ≃ Fin n) (A : MatroidProphet.OnlineRule n bits) :
    OnlineRule α n bits where
  decide k r s h := A.decide k r (s ∘ e.symm) (encodeHistory e h)
  measurable_decide k := by
    have hinput : Measurable (fun x : Seed bits × ((α → ℝ) × History α k) =>
        (x.1, (x.2.1 ∘ e.symm, encodeHistory e x.2.2))) := by
      apply Measurable.prodMk measurable_fst
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro i
        exact (measurable_pi_apply (e.symm i)).comp (measurable_fst.comp measurable_snd)
      · apply Measurable.of_eval
        intro j
        apply Measurable.prodMk
        · exact (measurable_of_finite e).comp
            (measurable_fst.comp ((measurable_pi_apply j).comp
              (measurable_snd.comp measurable_snd)))
        · exact measurable_snd.comp ((measurable_pi_apply j).comp
            (measurable_snd.comp measurable_snd))
    exact (A.measurable_decide k).comp hinput

def history (w : α → ℝ) (π : ArrivalOrder α n) (k : Fin n) : History α k :=
  fun j => let a := π (prefixIndex k j); (a, w a)

def decisionAt (A : OnlineRule α n bits) (r : Seed bits) (s w : α → ℝ)
    (π : ArrivalOrder α n) (k : Fin n) : Bool := A.decide k r s (history w π k)

noncomputable def acceptedThrough (A : OnlineRule α n bits) (r : Seed bits)
    (s w : α → ℝ) (π : ArrivalOrder α n) (t : ℕ) : Finset α := by
  classical
  exact univ.filter fun a => (π.symm a).val < t ∧ decisionAt A r s w π (π.symm a) = true

noncomputable def reward (A : OnlineRule α n bits) (r : Seed bits)
    (s w : α → ℝ) (π : ArrivalOrder α n) : ℝ :=
  ∑ a ∈ acceptedThrough A r s w π n, w a

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem encode_history (e : α ≃ Fin n) (w : α → ℝ) (π : ArrivalOrder α n)
    (k : Fin n) :
    encodeHistory e (history w π k) =
      MatroidProphet.history (w ∘ e.symm) (π.trans e) k := by
  ext j <;> simp [encodeHistory, history, MatroidProphet.history]

theorem decode_decision (e : α ≃ Fin n) (A : MatroidProphet.OnlineRule n bits)
    (r : Seed bits) (s w : α → ℝ) (π : ArrivalOrder α n) (k : Fin n) :
    decisionAt (decodeRule e A) r s w π k =
      MatroidProphet.decisionAt A r (s ∘ e.symm) (w ∘ e.symm) (π.trans e) k := by
  simp only [decisionAt, decodeRule, MatroidProphet.decisionAt, encode_history]

theorem decode_acceptedThrough (e : α ≃ Fin n) (A : MatroidProphet.OnlineRule n bits)
    (r : Seed bits) (s w : α → ℝ) (π : ArrivalOrder α n) (t : ℕ) :
    acceptedThrough (decodeRule e A) r s w π t =
      (MatroidProphet.acceptedThrough A r (s ∘ e.symm) (w ∘ e.symm)
        (π.trans e) t).map e.symm.toEmbedding := by
  classical
  ext label
  rw [Finset.mem_map_equiv]
  simp only [acceptedThrough, MatroidProphet.acceptedThrough, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp [decode_decision]

theorem decode_reward (e : α ≃ Fin n) (A : MatroidProphet.OnlineRule n bits)
    (r : Seed bits) (s w : α → ℝ) (π : ArrivalOrder α n) :
    reward (decodeRule e A) r s w π =
      MatroidProphet.reward A r (s ∘ e.symm) (w ∘ e.symm) (π.trans e) := by
  simp [reward, decode_acceptedThrough, MatroidProphet.reward, MatroidProphet.accepted]

/-- Prefix feasibility transports back to the original labels, including loops. -/
theorem decode_feasible (M : Matroid α) (e : α ≃ Fin n)
    (A : MatroidProphet.OnlineRule n bits) (hA : Feasible (M.mapEquiv e) A)
    (r : Seed bits) (s w : α → ℝ) (π : ArrivalOrder α n) (t : ℕ)
    (hs : ∀ a, 0 ≤ s a) (hw : ∀ a, 0 ≤ w a) :
    M.Indep (acceptedThrough (decodeRule e A) r s w π t : Set α) := by
  have h := hA r (s ∘ e.symm) (w ∘ e.symm) (π.trans e) t
    (fun i => hs (e.symm i)) (fun i => hw (e.symm i))
  rw [Matroid.mapEquiv_indep_iff] at h
  simpa [decode_acceptedThrough] using h

end MatroidProphet.LabeledTransport

end OAI
