import Mathlib
import OAI.Computability.MinUncut.PCP.Folding
import OAI.Computability.MinUncut.Encoding.BinaryLinear

namespace OAI

section
namespace MinUncutGames.Reduction.ActualSource

open MinUncutGames.Integration.BinaryLinear

structure Source where
  «variables» : Nat
  occurrences : Nat
  nonempty : 0 < occurrences
  equation : Fin occurrences → CloneGap.Equation (Fin «variables»)

def Source.sourceList (S : Source) : List (CloneGap.Equation (Fin S.«variables»)) :=
  List.ofFn S.equation

def Source.ofList {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) : Source where
  «variables» := n
  occurrences := es.length
  nonempty := List.length_pos_iff.mpr hne
  equation := es.get

@[simp] theorem Source.sourceList_ofList {n : Nat}
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (Source.ofList es hne).sourceList = es := by
  exact List.ofFn_getElem

@[simp] theorem Source.sourceList_length (S : Source) :
    S.sourceList.length = S.occurrences := by simp [Source.sourceList]

theorem Source.sourceList_nonempty (S : Source) : S.sourceList ≠ [] := by
  intro h
  have hp := S.nonempty
  have hn := S.sourceList_length
  rw [h] at hn
  simp only [List.length_nil] at hn
  omega

instance sourceIndexNonempty (S : Source) : Nonempty (Fin S.occurrences) :=
  ⟨⟨0, S.nonempty⟩⟩

def Source.satisfied (S : Source) (A : Fin S.«variables» → Bool)
    (i : Fin S.occurrences) : Bool := CloneGap.satisfied (S.equation i) A

def Source.failure (S : Source) (A : Fin S.«variables» → Bool) : ℚ :=
  Finset.univ.expect (fun i => if S.satisfied A i then (0 : ℚ) else 1)

def Source.DistinctNames (S : Source) : Prop :=
  ∀ i, (S.equation i).first ≠ (S.equation i).second ∧
    (S.equation i).first ≠ (S.equation i).third ∧
    (S.equation i).second ≠ (S.equation i).third

abbrev Alphabet (s : Nat) := MinUncutGames.Integration.BinaryLinear.Vector s
abbrev Ambient (s d : Nat) := Alphabet s × MinUncutGames.Integration.BinaryLinear.Vector d

def alphabetEmbedding (s d : Nat) : Alphabet s →ₗ[F2] Ambient s d :=
  LinearMap.inl F2 (Alphabet s) (MinUncutGames.Integration.BinaryLinear.Vector d)

@[simp] theorem alphabetEmbedding_apply (s d : Nat) (c : Alphabet s) :
    alphabetEmbedding s d c = (c, 0) := rfl

structure SplitGadget (s d : Nat) where
  f : Ambient s d → Alphabet s
  equivariant : ∀ (x : Ambient s d) (c : Alphabet s), f (x + (c, 0)) = f x + c
  NoiseIndex : Type
  noiseFintype : Fintype NoiseIndex
  noiseNonempty : Nonempty NoiseIndex
  noise : NoiseIndex → Ambient s d

attribute [instance] SplitGadget.noiseFintype SplitGadget.noiseNonempty

def SplitGadget.stabilityError {s d : Nat} (g : SplitGadget s d) : ℚ :=
  Finset.univ.expect (fun xv : Ambient s d × g.NoiseIndex =>
    if g.f (xv.1 + g.noise xv.2) = g.f xv.1 then (0 : ℚ) else 1)

def SplitGadget.kernelError {s d p : Nat} (g : SplitGadget s d)
    (S : Ambient s d →ₗ[F2] MinUncutGames.Integration.BinaryLinear.Vector p) : ℚ :=
  Finset.univ.expect (fun i => if S (g.noise i) = 0 then (1 : ℚ) else 0)

theorem SplitGadget.stabilityError_nonneg {s d : Nat} (g : SplitGadget s d) :
    0 ≤ g.stabilityError := by
  apply Finset.expect_nonneg
  intro x _
  split <;> norm_num

theorem SplitGadget.stabilityError_le_one {s d : Nat} (g : SplitGadget s d) :
    g.stabilityError ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  split <;> norm_num

end MinUncutGames.Reduction.ActualSource

end
section
namespace MinUncutGames.Reduction.Incidence

universe u v
variable {Variable : Type u} {Index : Type v}

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

def parity (a : Triple) : Bool := (a.first.xor a.second).xor a.third

def matchingSlots (a b : Triple) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

def acceptedSlots (a b : Triple) (rhs : Bool) : Nat :=
  if parity a = rhs then matchingSlots a b else 0

def failedEquation (b : Triple) (rhs : Bool) : Nat :=
  if parity b = rhs then 0 else 1

def bestResponse (b : Triple) (rhs : Bool) : Triple :=
  if parity b = rhs then b else { b with first := !b.first }

theorem local_count_bound (a b : Triple) (rhs : Bool) :
    acceptedSlots a b rhs + failedEquation b rhs ≤ 3 := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases rhs <;> decide

theorem best_response_exact (b : Triple) (rhs : Bool) :
    acceptedSlots (bestResponse b rhs) b rhs + failedEquation b rhs = 3 := by
  rcases b with ⟨b₁, b₂, b₃⟩
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases rhs <;> decide

structure Equation (Variable : Type u) where
  first : Variable
  second : Variable
  third : Variable
  rhs : Bool

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def nameAt (e : Equation Variable) : Slot → Variable
  | .first => e.first
  | .second => e.second
  | .third => e.third

def bitAt (a : Triple) : Slot → Bool
  | .first => a.first
  | .second => a.second
  | .third => a.third

def questionPredicate (e : Equation Variable) (name : Variable)
    (alice : Triple) (bob : Bool) : Prop :=
  parity alice = e.rhs ∧
    ((e.first = name ∧ alice.first = bob) ∨
     (e.second = name ∧ alice.second = bob) ∨
     (e.third = name ∧ alice.third = bob))

theorem question_predicate_at_slot (e : Equation Variable)
    (distinct₁₂ : e.first ≠ e.second) (distinct₁₃ : e.first ≠ e.third)
    (distinct₂₃ : e.second ≠ e.third) (alice : Triple) (bob : Bool) (slot : Slot) :
    questionPredicate e (nameAt e slot) alice bob ↔
      parity alice = e.rhs ∧ bitAt alice slot = bob := by
  cases slot <;>
    simp [questionPredicate, nameAt, bitAt, distinct₁₂, distinct₁₃, distinct₂₃,
      Ne.symm distinct₁₂, Ne.symm distinct₁₃, Ne.symm distinct₂₃]

def bobTriple (g : Variable → Bool) (e : Equation Variable) : Triple :=
  ⟨g e.first, g e.second, g e.third⟩

def acceptedCount (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) : List Index → Nat
  | [] => 0
  | i :: rest =>
    acceptedSlots (alice i) (bobTriple g (equations i)) (equations i).rhs +
      acceptedCount equations g alice rest

def failureCount (equations : Index → Equation Variable)
    (g : Variable → Bool) : List Index → Nat
  | [] => 0
  | i :: rest =>
    failedEquation (bobTriple g (equations i)) (equations i).rhs +
      failureCount equations g rest

theorem total_count_bound (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) (occurrences : List Index) :
    acceptedCount equations g alice occurrences + failureCount equations g occurrences ≤
      3 * occurrences.length := by
  induction occurrences with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := local_count_bound (alice i) (bobTriple g (equations i)) (equations i).rhs
    simp only [acceptedCount, failureCount, List.length_cons]
    omega

def optimalAlice (equations : Index → Equation Variable) (g : Variable → Bool)
    (i : Index) : Triple :=
  bestResponse (bobTriple g (equations i)) (equations i).rhs

theorem optimal_alice_exact (equations : Index → Equation Variable)
    (g : Variable → Bool) (occurrences : List Index) :
    acceptedCount equations g (optimalAlice equations g) occurrences +
      failureCount equations g occurrences = 3 * occurrences.length := by
  induction occurrences with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := best_response_exact (bobTriple g (equations i)) (equations i).rhs
    simp only [acceptedCount, failureCount, List.length_cons, optimalAlice]
    omega

theorem fixed_bob_optimum (equations : Index → Equation Variable)
    (g : Variable → Bool) (occurrences : List Index) :
    ∃ alice : Index → Triple,
      acceptedCount equations g alice occurrences + failureCount equations g occurrences =
        3 * occurrences.length ∧
      ∀ other : Index → Triple,
        acceptedCount equations g other occurrences ≤
          acceptedCount equations g alice occurrences := by
  refine ⟨optimalAlice equations g, optimal_alice_exact equations g occurrences, ?_⟩
  intro other
  have h := total_count_bound equations g other occurrences
  have heq := optimal_alice_exact equations g occurrences
  omega

theorem soundness_191_over_192 (equations : Index → Equation Variable)
    (g : Variable → Bool) (alice : Index → Triple) (occurrences : List Index)
    (source_gap : occurrences.length ≤ 64 * failureCount equations g occurrences) :
    64 * acceptedCount equations g alice occurrences ≤ 191 * occurrences.length := by
  have h := total_count_bound equations g alice occurrences
  omega

theorem game_soundness_191_over_192 (equations : Index → Equation Variable)
    (occurrences : List Index)
    (source_gap : ∀ g : Variable → Bool,
      occurrences.length ≤ 64 * failureCount equations g occurrences) :
    ∀ (g : Variable → Bool) (alice : Index → Triple),
      64 * acceptedCount equations g alice occurrences ≤ 191 * occurrences.length := by
  intro g alice
  exact soundness_191_over_192 equations g alice occurrences (source_gap g)

end MinUncutGames.Reduction.Incidence

end
section
namespace MinUncutGames.Reduction.SourceIncidence

variable {Name : Type} {Index : Type*}

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

end MinUncutGames.Reduction.SourceIncidence

end
section
namespace MinUncutGames.Reduction.FiniteSource

open CloneGap

variable {n : ℕ} {α β : Type*}

abbrev Name (s : ActualSource.Source) := Fin s.«variables» × Fin 48

def clonedSource (s : ActualSource.Source) := cloneList s.sourceList

abbrev Occurrence (s : ActualSource.Source) := Fin (clonedSource s).length

def occurrences (s : ActualSource.Source) : List (Occurrence s) :=
  List.finRange (clonedSource s).length

def rawEquation (s : ActualSource.Source) (i : Occurrence s) : Equation (Fin s.«variables» × Nat) :=
  (clonedSource s)[i.val]

def finiteName (s : ActualSource.Source) (v : Fin s.«variables» × Nat) : Name s :=
  (v.1, ⟨v.2 % 48, Nat.mod_lt _ (by decide)⟩)

def mapEquation {α β : Type} (f : α → β) (e : Equation α) : Equation β :=
  ⟨f e.first, f e.second, f e.third, e.rhs⟩

def equation (s : ActualSource.Source) (i : Occurrence s) : Equation (Name s) :=
  mapEquation (finiteName s) (rawEquation s i)

theorem satisfied_map {α β : Type} (f : α → β) (e : Equation α) (g : β → Bool) :
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
    {u v : Fin s.«variables» × Nat} (hu : u.2 < 48) (hv : v.2 < 48)
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
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) :
    (occurrences s).length ≤
      64 * (occurrences s).countP (fun i => !satisfied (equation s i) g) := by
  rw [occurrences_length, indexed_failure_count]
  exact clone_gap s.sourceList source_gap (g ∘ finiteName s)

theorem indexed_completeness_count (s : ActualSource.Source) (A : Fin s.«variables» → Bool) :
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
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) :
    (occurrences s).length ≤
      64 * Incidence.failureCount (incidenceEquation s) g (occurrences s) := by
  unfold incidenceEquation
  rw [SourceIncidence.failureCount_eq]
  exact indexed_gap s source_gap g

theorem incidence_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) (alice : Occurrence s → Incidence.Triple) :
    64 * Incidence.acceptedCount (incidenceEquation s) g alice (occurrences s) ≤
      191 * (occurrences s).length :=
  Incidence.soundness_191_over_192 _ g alice _ (incidence_failure_gap s source_gap g)

def nameEquiv (s : ActualSource.Source) : Name s ≃ Fin (s.«variables» * 48) :=
  finProdFinEquiv

def cloned (s : ActualSource.Source) : ActualSource.Source where
  «variables» := s.«variables» * 48
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
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (A : Fin (cloned s).«variables» → Bool) :
    (cloned s).sourceList.length ≤
      64 * (cloned s).sourceList.countP (fun e => !satisfied e A) := by
  change Fin (s.«variables» * 48) → Bool at A
  have h := indexed_gap s source_gap (A ∘ nameEquiv s)
  rw [occurrences_length] at h
  change (List.ofFn (fun i => mapEquation (nameEquiv s) (equation s i))).length ≤
    64 * (List.ofFn (fun i => mapEquation (nameEquiv s) (equation s i))).countP
      (fun e => !satisfied e A)
  rw [List.length_ofFn, count_ofFn]
  exact h

theorem cloned_completeness_count (s : ActualSource.Source) (A : Fin s.«variables» → Bool) :
    (cloned s).sourceList.countP
      (fun e => satisfied e (fun z => A ((nameEquiv s).symm z).1)) =
      s.sourceList.countP (fun e => satisfied e A) * distinctTriples.length := by
  have h := indexed_completeness_count s A
  simpa only [ActualSource.Source.sourceList, count_ofFn, cloned, satisfied_map,
    Function.comp_def, Equiv.symm_apply_apply, occurrences] using h

end MinUncutGames.Reduction.FiniteSource

end
section
namespace MinUncutGames.Soundness.IncidenceExtraction

abbrev Triple := Fin 3 → Bool

def xorTriple (x : Triple) : Bool := (x 0 ^^ x 1) ^^ x 2

structure Incidence (Occurrence Name : Type) where
  name : Occurrence → Fin 3 → Name
  rhs : Occurrence → Bool

def Incidence.accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) : Prop :=
  xorTriple a = g.rhs o ∧ a i = b

def Incidence.namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (n : Name)
    (a : Triple) (b : Bool) : Prop :=
  ∃ i, g.name o i = n ∧ g.accepts o i a b

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

theorem Incidence.namedAccepts_iff_accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (o : Occurrence) (i : Fin 3) (a : Triple) (b : Bool) :
    g.namedAccepts o (g.name o i) a b ↔ g.accepts o i a b := by
  constructor
  · rintro ⟨j, hname, h⟩
    have hji := distinct o j i hname
    simpa [hji] using h
  · exact g.accepts_implies_namedAccepts o i a b

structure FullPoint (Position : Type) where
  homogeneous : Bool
  coords : Position → Triple

def FullPoint.valid {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (e : FullPoint Position) : Prop :=
  ∀ j, xorTriple (e.coords j) = (g.rhs (u j) && e.homogeneous)

structure PartnerPoint (Position : Type) where
  homogeneous : Bool
  single : Position → Bool

def AugmentedAccepts {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active : Position → Prop) (slot : Position → Fin 3)
    (eA : FullPoint Position) (eB : PartnerPoint Position) : Prop :=
  eA.valid g u ∧ eA.homogeneous = true ∧ eB.homogeneous = true ∧
  ∀ j, active j → eA.coords j (slot j) = eB.single j

def RepeatedAccepts {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (slot : Position → Fin 3) (inside : Position → Prop)
    (answerA : Position → Triple) (answerB : Position → Bool) : Prop :=
  ∀ j, inside j → g.accepts (u j) (slot j) (answerA j) (answerB j)

theorem augmented_accepts_implies_repeated_accepts
    {Position Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active inside : Position → Prop) (slot : Position → Fin 3)
    (eA : FullPoint Position) (eB : PartnerPoint Position)
    (hinside : ∀ j, inside j → active j)
    (haccept : AugmentedAccepts g u active slot eA eB) :
    RepeatedAccepts g u slot inside eA.coords eB.single := by
  obtain ⟨hvalid, hone, _, hagree⟩ := haccept
  intro j hj
  constructor
  · have heq := hvalid j
    simpa [hone] using heq
  · exact hagree j (hinside j hj)

theorem augmented_accepts_implies_named_repeated_accepts
    {Position RepeatPosition Occurrence Name : Type}
    (g : Incidence Occurrence Name) (u : Position → Occurrence)
    (active : Position → Prop) (slot : Position → Fin 3)
    (embed : RepeatPosition → Position)
    (eA : FullPoint Position) (eB : PartnerPoint Position)
    (hinside : ∀ r, active (embed r))
    (haccept : AugmentedAccepts g u active slot eA eB) :
    ∀ r, g.namedAccepts (u (embed r))
      (g.name (u (embed r)) (slot (embed r)))
      (eA.coords (embed r)) (eB.single (embed r)) := by
  intro r
  apply g.accepts_implies_namedAccepts
  obtain ⟨hvalid, hone, _, hagree⟩ := haccept
  constructor
  · have heq := hvalid (embed r)
    simpa [hone] using heq
  · exact hagree (embed r) (hinside r)

structure Game (QA QB A B : Type) where
  accepts : QA → QB → A → B → Prop

structure Strategies (QA QB A B : Type) where
  first : QA → A
  second : QB → B

def Strategies.wins {QA QB A B : Type} (s : Strategies QA QB A B)
    (g : Game QA QB A B) (qa : QA) (qb : QB) : Prop :=
  g.accepts qa qb (s.first qa) (s.second qb)

structure LocalSimulation
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    (inner : Game InnerQA InnerQB InnerA InnerB)
    (outer : Game OuterQA OuterQB OuterA OuterB) where
  questionA : InnerQA → OuterQA
  questionB : InnerQB → OuterQB
  answerA : InnerQA → OuterA → InnerA
  answerB : InnerQB → OuterB → InnerB
  sound : ∀ qa qb a b,
    outer.accepts (questionA qa) (questionB qb) a b →
    inner.accepts qa qb (answerA qa a) (answerB qb b)

def LocalSimulation.induced
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB) :
    Strategies InnerQA InnerQB InnerA InnerB where
  first qa := r.answerA qa (s.first (r.questionA qa))
  second qb := r.answerB qb (s.second (r.questionB qb))

theorem LocalSimulation.induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB)
    (qa : InnerQA) (qb : InnerQB)
    (hwins : s.wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced s).wins inner qa qb :=
  r.sound qa qb (s.first (r.questionA qa)) (s.second (r.questionB qb)) hwins

theorem LocalSimulation.seeded_induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB Seed : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (strategy : Seed → Strategies OuterQA OuterQB OuterA OuterB)
    (seed : Seed) (qa : InnerQA) (qb : InnerQB)
    (hwins : (strategy seed).wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced (strategy seed)).wins inner qa qb :=
  r.induced_wins (strategy seed) qa qb hwins

end MinUncutGames.Soundness.IncidenceExtraction

end

end OAI
