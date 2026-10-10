import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationMetadataBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters.FrequencyExposure

def pairedFrequencyProduct {l : ℕ} (h h' : History l) : ℕ :=
  FrequencyPrecision.product (h.frequencies ++ h'.frequencies)

theorem root_frequency_mem {l : ℕ} (h : History l) :
    h.root.frequency ∈ h.frequencies := by
  cases h <;> simp [History.root, History.frequencies]

theorem left_frequency_mem {l : ℕ} (a : State) (pivot : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) {s : ℤ}
    (hs : s ∈ left.frequencies) :
    s ∈ (History.node a pivot u hp hm left right).frequencies := by
  simp only [History.frequencies, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl hs)

theorem right_frequency_mem {l : ℕ} (a : State) (pivot : ℕ)
    (u hp hm : List SmallSlot) (left right : History l) {s : ℤ}
    (hs : s ∈ right.frequencies) :
    s ∈ (History.node a pivot u hp hm left right).frequencies := by
  simp only [History.frequencies, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr hs)

def actualNodeData (R : ℕ) (s s' v w v' w' : ℤ)
    (hs : s.natAbs ∣ R) (hs' : s'.natAbs ∣ R) : Data R :=
  ⟨s, s', v, w, v', w', hs, hs'⟩

def frequencyScheduleAux (R : ℕ) : {l : ℕ} → (h h' : History l) →
    (∀ s ∈ h.frequencies, s.natAbs ∣ R) →
    (∀ s ∈ h'.frequencies, s.natAbs ∣ R) → List Bool → Data R
  | _, .leaf a, .leaf a', hh, hh' => fun _ =>
    actualNodeData R a.frequency a'.frequency a.frequency a.frequency a'.frequency a'.frequency
      (hh _ (by simp [History.frequencies])) (hh' _ (by simp [History.frequencies]))
  | _, .node a pivot u hp hm left right, .node a' pivot' u' hp' hm' left' right', hh, hh' =>
    reverseAddressSchedule
      (actualNodeData R a.frequency a'.frequency left.root.frequency right.root.frequency
        left'.root.frequency right'.root.frequency
        (hh _ (by simp [History.frequencies])) (hh' _ (by simp [History.frequencies])))
      (frequencyScheduleAux R left left'
        (fun s hs => hh s (left_frequency_mem a pivot u hp hm left right hs))
        (fun s hs => hh' s (left_frequency_mem a' pivot' u' hp' hm' left' right' hs)))
      (frequencyScheduleAux R right right'
        (fun s hs => hh s (right_frequency_mem a pivot u hp hm left right hs))
        (fun s hs => hh' s (right_frequency_mem a' pivot' u' hp' hm' left' right' hs)))

def fixedFactorSchedule : {l : ℕ} → History l → History l →
    List Bool → FixedFactors × FixedFactors
  | _, .leaf _, .leaf _ => fun _ => (⟨1, 1, 1⟩, ⟨1, 1, 1⟩)
  | _, .node _ _ u hp hm left right, .node _ _ u' hp' hm' left' right' =>
    reverseAddressSchedule
      (⟨fixedProduct hp, fixedProduct hm, (u.map SmallSlot.value).prod⟩,
       ⟨fixedProduct hp', fixedProduct hm', (u'.map SmallSlot.value).prod⟩)
      (fixedFactorSchedule left left') (fixedFactorSchedule right right')

theorem frequencyScheduleAux_matches (R : ℕ) {l : ℕ} (h h' : History l)
    (hh : ∀ s ∈ h.frequencies, s.natAbs ∣ R)
    (hh' : ∀ s ∈ h'.frequencies, s.natAbs ∣ R) :
    ScheduleMatches (frequencyScheduleAux R h h' hh hh') (fixedFactorSchedule h h') [] h h' := by
  induction h with
  | leaf a => cases h'; trivial
  | @node l a pivot u hp hm left right ihl ihr =>
    cases h' with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [ScheduleMatches]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · rw [← List.nil_append [false]]
        apply (scheduleMatches_append_iff _ _ [] [false] left left').mp
        simpa only [frequencyScheduleAux, fixedFactorSchedule,
          reverseAddressSchedule_append_false] using
          ihl left'
            (fun s hs => hh s (left_frequency_mem a pivot u hp hm left right hs))
            (fun s hs => hh' s (left_frequency_mem a' pivot' u' hp' hm' left' right' hs))
      · rw [← List.nil_append [true]]
        apply (scheduleMatches_append_iff _ _ [] [true] right right').mp
        simpa only [frequencyScheduleAux, fixedFactorSchedule,
          reverseAddressSchedule_append_true] using
          ihr right'
            (fun s hs => hh s (right_frequency_mem a pivot u hp hm left right hs))
            (fun s hs => hh' s (right_frequency_mem a' pivot' u' hp' hm' left' right' hs))

def frequencySchedule {l : ℕ} (h h' : History l) : List Bool → Data (pairedFrequencyProduct h h') :=
  frequencyScheduleAux (pairedFrequencyProduct h h') h h'
    (fun _ hs => FrequencyPrecision.frequency_dvd_product (List.mem_append_left _ hs))
    (fun _ hs => FrequencyPrecision.frequency_dvd_product (List.mem_append_right _ hs))

theorem canonical_scheduleMatches {l : ℕ} (h h' : History l) :
    ScheduleMatches (frequencySchedule h h') (fixedFactorSchedule h h') [] h h' :=
  frequencyScheduleAux_matches _ h h' _ _

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
