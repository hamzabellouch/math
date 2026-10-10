import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas
import OAI.Computability.UniqueGames.Reduction.GameEncodingSizeLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.SourceIncidence

variable {Name Index : Type}

def toIncidence (e : CloneGap.Equation Name) : Incidence.Equation Name :=
  ⟨e.first, e.second, e.third, e.rhs⟩

theorem failedEquation_eq (e : CloneGap.Equation Name) (g : Name → Bool) :
    Incidence.failedEquation (Incidence.bobTriple g (toIncidence e)) (toIncidence e).rhs =
      if CloneGap.satisfied e g then 0 else 1 := by
  simp only [Incidence.failedEquation, Incidence.bobTriple, toIncidence,
    Incidence.parity, CloneGap.satisfied]
  simp

theorem failureCount_eq (equations : Index → CloneGap.Equation Name)
    (g : Name → Bool) (occurrences : List Index) :
    Incidence.failureCount (fun i => toIncidence (equations i)) g occurrences =
      occurrences.countP (fun i => !CloneGap.satisfied (equations i) g) := by
  induction occurrences with
  | nil => rfl
  | cons i rest ih =>
    simp only [Incidence.failureCount, failedEquation_eq, ih, List.countP_cons]
    cases CloneGap.satisfied (equations i) g <;> simp
    omega

/-- The full occurrence is the displayed equation together with a fresh index. -/
def occurrenceList (source : List (CloneGap.Equation Name)) :=
  (CloneGap.cloneList source).zipIdx

theorem cloned_occurrence_gap (source : List (CloneGap.Equation Name))
    (source_gap : ∀ A : Name → Bool,
      source.length ≤ 4 * source.countP (fun e => !CloneGap.satisfied e A))
    (g : Name × CloneGap.Index → Bool) :
    (occurrenceList source).length ≤ 64 *
      Incidence.failureCount (fun i => toIncidence i.1) g (occurrenceList source) := by
  have hg := CloneGap.clone_gap source source_gap g
  rw [failureCount_eq]
  unfold occurrenceList
  rw [List.length_zipIdx]
  have hcount : ((CloneGap.cloneList source).zipIdx).countP
      (fun i => !CloneGap.satisfied i.1 g) =
      (CloneGap.cloneList source).countP (fun e => !CloneGap.satisfied e g) := by
    have h := congrArg (fun es => es.countP (fun e => !CloneGap.satisfied e g))
      (List.zipIdx_map_fst 0 (CloneGap.cloneList source))
    simpa only [List.countP_map, Function.comp_def] using h
  rw [hcount]
  exact hg

theorem source_to_incidence_soundness (source : List (CloneGap.Equation Name))
    (source_gap : ∀ A : Name → Bool,
      source.length ≤ 4 * source.countP (fun e => !CloneGap.satisfied e A))
    (g : Name × CloneGap.Index → Bool)
    (alice : CloneGap.Equation (Name × CloneGap.Index) × Nat → Incidence.Triple) :
    64 * Incidence.acceptedCount (fun i => toIncidence i.1) g alice
      (occurrenceList source) ≤ 191 * (occurrenceList source).length := by
  exact Incidence.soundness_191_over_192 _ g alice _
    (cloned_occurrence_gap source source_gap g)

end UniqueGamesTheorem.Reduction.SourceIncidence

end

section

namespace UniqueGamesTheorem.Reduction.FiniteSource

open CloneGap

variable {α β : Type} {n : Nat}

abbrev Name (s : ActualSource.Source) := Fin s.variables × Fin 48

def clonedSource (s : ActualSource.Source) := cloneList s.sourceList

abbrev Occurrence (s : ActualSource.Source) := Fin (clonedSource s).length

def occurrences (s : ActualSource.Source) : List (Occurrence s) :=
  List.finRange (clonedSource s).length

def rawEquation (s : ActualSource.Source) (i : Occurrence s) : Equation (Fin s.variables × Nat) :=
  (clonedSource s)[i.val]

/-- Total conversion; membership proofs below establish that every index used
    by the construction is already below 48, so the remainder changes none. -/
def finiteName (s : ActualSource.Source) (v : Fin s.variables × Nat) : Name s :=
  (v.1, ⟨v.2 % 48, Nat.mod_lt _ (by decide)⟩)

def mapEquation (f : α → β) (e : Equation α) : Equation β :=
  ⟨f e.first, f e.second, f e.third, e.rhs⟩

def equation (s : ActualSource.Source) (i : Occurrence s) : Equation (Name s) :=
  mapEquation (finiteName s) (rawEquation s i)

theorem satisfied_map (f : α → β) (e : Equation α) (g : β → Bool) :
    satisfied (mapEquation f e) g = satisfied e (g ∘ f) := rfl

theorem mem_cart {xs : List α} {ys : List β} {z : α × β} :
    z ∈ cart xs ys ↔ z.1 ∈ xs ∧ z.2 ∈ ys := by
  simp only [cart, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    cases h
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨z.1, hx, z.2, hy, rfl⟩

theorem distinctTriple_bounds {t : Nat × Nat × Nat} (h : t ∈ distinctTriples) :
    t.1 < 48 ∧ t.2.1 < 48 ∧ t.2.2 < 48 := by
  have h := (List.mem_filter.mp h).1
  change t ∈ cart indices (cart indices indices) at h
  rw [mem_cart, mem_cart] at h
  simpa [indices] using h

theorem distinctTriples_nonempty : 0 < distinctTriples.length := by
  have hm : (0, 1, 2) ∈ distinctTriples := by
    simp [distinctTriples, triples, mem_cart, indices, collision]
  exact List.length_pos_iff_exists_mem.mpr ⟨_, hm⟩

theorem cloned_member_properties {source : List (Equation (Fin n))}
    {e : Equation (Fin n × Nat)} (h : e ∈ cloneList source) :
    (e.first.2 < 48 ∧ e.second.2 < 48 ∧ e.third.2 < 48) ∧
    (e.first ≠ e.second ∧ e.first ≠ e.third ∧ e.second ≠ e.third) := by
  obtain ⟨old, _, h⟩ := List.mem_flatMap.mp h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  have hb := distinctTriple_bounds ht
  have hc : collision t = false := by
    simpa using (List.mem_filter.mp ht).2
  exact ⟨hb, clone_names_distinct old t hc⟩

theorem raw_properties (s : ActualSource.Source) (i : Occurrence s) :
    ((rawEquation s i).first.2 < 48 ∧ (rawEquation s i).second.2 < 48 ∧
      (rawEquation s i).third.2 < 48) ∧
    ((rawEquation s i).first ≠ (rawEquation s i).second ∧
      (rawEquation s i).first ≠ (rawEquation s i).third ∧
      (rawEquation s i).second ≠ (rawEquation s i).third) := by
  apply cloned_member_properties
  exact List.getElem_mem i.isLt

theorem finiteName_injective_on (s : ActualSource.Source)
    {u v : Fin s.variables × Nat} (hu : u.2 < 48) (hv : v.2 < 48)
    (h : finiteName s u = finiteName s v) : u = v := by
  have he := congrArg (fun z : Name s => (z.1, z.2.val)) h
  simpa [finiteName, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using he

theorem names_distinct (s : ActualSource.Source) (i : Occurrence s) :
    (equation s i).first ≠ (equation s i).second ∧
    (equation s i).first ≠ (equation s i).third ∧
    (equation s i).second ≠ (equation s i).third := by
  obtain ⟨⟨h₁, h₂, h₃⟩, ⟨h₁₂, h₁₃, h₂₃⟩⟩ := raw_properties s i
  exact ⟨fun h => h₁₂ (finiteName_injective_on s h₁ h₂ h),
    fun h => h₁₃ (finiteName_injective_on s h₁ h₃ h),
    fun h => h₂₃ (finiteName_injective_on s h₂ h₃ h)⟩

theorem raw_map_occurrences (s : ActualSource.Source) :
    (occurrences s).map (rawEquation s) = clonedSource s := by
  simp [occurrences, List.finRange, List.map_ofFn, rawEquation, Function.comp_def]

theorem occurrences_length (s : ActualSource.Source) :
    (occurrences s).length = (clonedSource s).length := by
  simp [occurrences]

theorem clonedSource_nonempty (s : ActualSource.Source) : 0 < (clonedSource s).length := by
  rw [clonedSource, length_cloneList]
  have hs : 0 < s.sourceList.length := by
    simpa [ActualSource.Source.sourceList] using s.nonempty
  exact Nat.mul_pos hs distinctTriples_nonempty

instance (s : ActualSource.Source) : Nonempty (Occurrence s) :=
  ⟨⟨0, clonedSource_nonempty s⟩⟩

theorem indexed_failure_count (s : ActualSource.Source) (g : Name s → Bool) :
    (occurrences s).countP (fun i => !satisfied (equation s i) g) =
      (clonedSource s).countP (fun e => !satisfied e (g ∘ finiteName s)) := by
  have h := congrArg (fun es => es.countP
    (fun e => !satisfied e (g ∘ finiteName s))) (raw_map_occurrences s)
  simpa only [List.countP_map, Function.comp_def, equation, satisfied_map] using h

theorem indexed_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) :
    (occurrences s).length ≤
      64 * (occurrences s).countP (fun i => !satisfied (equation s i) g) := by
  rw [occurrences_length, indexed_failure_count]
  exact clone_gap s.sourceList source_gap (g ∘ finiteName s)

theorem indexed_completeness_count (s : ActualSource.Source) (A : Fin s.variables → Bool) :
    (occurrences s).countP (fun i => satisfied (equation s i) (fun z => A z.1)) =
      s.sourceList.countP (fun e => satisfied e A) * distinctTriples.length := by
  have h := congrArg (fun es => es.countP
    (fun e => satisfied e (fun z => A z.1))) (raw_map_occurrences s)
  simp only [List.countP_map, Function.comp_def] at h
  change (occurrences s).countP
    (fun i => satisfied (rawEquation s i) (fun z => A z.1)) = _
  rw [h]
  exact clone_completeness_count s.sourceList A

def incidenceEquation (s : ActualSource.Source) (i : Occurrence s) :
    Incidence.Equation (Name s) := SourceIncidence.toIncidence (equation s i)

theorem incidence_question_predicate (s : ActualSource.Source) (i : Occurrence s)
    (alice : Incidence.Triple) (bob : Bool) (slot : Incidence.Slot) :
    Incidence.questionPredicate (incidenceEquation s i)
      (Incidence.nameAt (incidenceEquation s i) slot) alice bob ↔
      Incidence.parity alice = (incidenceEquation s i).rhs ∧
        Incidence.bitAt alice slot = bob := by
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := names_distinct s i
  exact Incidence.question_predicate_at_slot _ h₁₂ h₁₃ h₂₃ alice bob slot

theorem incidence_failure_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) :
    (occurrences s).length ≤
      64 * Incidence.failureCount (incidenceEquation s) g (occurrences s) := by
  unfold incidenceEquation
  rw [SourceIncidence.failureCount_eq]
  exact indexed_gap s source_gap g

theorem incidence_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) (alice : Occurrence s → Incidence.Triple) :
    64 * Incidence.acceptedCount (incidenceEquation s) g alice (occurrences s) ≤
      191 * (occurrences s).length :=
  Incidence.soundness_191_over_192 _ g alice _ (incidence_failure_gap s source_gap g)

/-- Executable row-major encoding of the finite clone names. -/
def nameEquiv (s : ActualSource.Source) : Name s ≃ Fin (s.variables * 48) :=
  finProdFinEquiv

def cloned (s : ActualSource.Source) : ActualSource.Source where
  «variables» := s.variables * 48
  occurrences := (clonedSource s).length
  nonempty := clonedSource_nonempty s
  equation i := mapEquation (nameEquiv s) (equation s i)

theorem cloned_length (s : ActualSource.Source) :
    (cloned s).occurrences = s.occurrences * distinctTriples.length := by
  change (cloneList s.sourceList).length = _
  rw [length_cloneList, ActualSource.Source.sourceList_length]

theorem cloned_distinct (s : ActualSource.Source) : (cloned s).DistinctNames := by
  intro i
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := names_distinct s i
  exact ⟨fun h => h₁₂ ((nameEquiv s).injective h),
    fun h => h₁₃ ((nameEquiv s).injective h),
    fun h => h₂₃ ((nameEquiv s).injective h)⟩

theorem count_ofFn (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = (List.finRange n).countP (fun i => p (f i)) := by
  have he : (List.finRange n).map f = List.ofFn f := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  have h := congrArg (fun es => es.countP p) he
  simpa only [List.countP_map, Function.comp_def] using h.symm

theorem cloned_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (A : Fin (cloned s).variables → Bool) :
    (cloned s).sourceList.length ≤
      64 * (cloned s).sourceList.countP (fun e => !satisfied e A) := by
  change Fin (s.variables * 48) → Bool at A
  have h := indexed_gap s source_gap (A ∘ nameEquiv s)
  rw [occurrences_length] at h
  change (List.ofFn (fun i => mapEquation (nameEquiv s) (equation s i))).length ≤
    64 * (List.ofFn (fun i => mapEquation (nameEquiv s) (equation s i))).countP
      (fun e => !satisfied e A)
  rw [List.length_ofFn, count_ofFn]
  exact h

theorem cloned_completeness_count (s : ActualSource.Source) (A : Fin s.variables → Bool) :
    (cloned s).sourceList.countP
      (fun e => satisfied e (fun z => A ((nameEquiv s).symm z).1)) =
      s.sourceList.countP (fun e => satisfied e A) * distinctTriples.length := by
  have h := indexed_completeness_count s A
  simpa only [ActualSource.Source.sourceList, count_ofFn, cloned, satisfied_map,
    Function.comp_def, Equiv.symm_apply_apply, occurrences] using h

end UniqueGamesTheorem.Reduction.FiniteSource

end

end OAI
