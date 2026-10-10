import Mathlib.Data.Fintype.EquivFin
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionReconstruction
import OAI.Computability.PerfectCompleteness.Foundations.CoordinateReplacementLemmas
import OAI.Computability.PerfectCompleteness.Foundations.DesignatedLeavesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedCardinality
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.SourceOddListsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutCallsLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanTreeFactors
import OAI.Computability.PerfectCompleteness.Sampling.UniformLatent

namespace OAI


namespace PerfectCompleteness.CutChildCleanLaw

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays ProjectedCardinality

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (ids : Slots branch n → Fin t → Nat)

abbrev Raw :=
  (C → squareSpace (H (projectedSlots ids))) × Arrays (projectedSlots ids) rows

instance rawFintype : Fintype (Raw (C := C) rows ids) := Fintype.ofFinite _

def zeroRaw : Raw (C := C) rows ids := (fun _ => 0, fun _ _ => 0)

instance rawNonempty : Nonempty (Raw (C := C) rows ids) := ⟨zeroRaw rows ids⟩

def rawEquiv : Raw (C := C) rows ids ≃ CleanTreeFactors.Raw (Fintype.card C) rows ids where
  toFun x := (fun q => x.1 ((Fintype.equivFin C).symm q), x.2)
  invFun x := (fun q => x.1 (Fintype.equivFin C q), x.2)
  left_inv x := by
    apply Prod.ext
    · funext q
      exact congrArg x.1 ((Fintype.equivFin C).symm_apply_apply q)
    · rfl
  right_inv x := by
    apply Prod.ext
    · funext q
      exact congrArg x.1 ((Fintype.equivFin C).apply_symm_apply q)
    · rfl

def allZero (x : Raw (C := C) rows ids) : Bool :=
  decide ((∀ q, x.1 q = 0) ∧ ∀ node row, x.2 node row = 0)

theorem allZero_rawEquiv (x : Raw (C := C) rows ids) :
    CleanTreeFactors.allZero (Fintype.card C) rows ids (rawEquiv rows ids x) =
      allZero rows ids x := by
  apply Bool.eq_iff_iff.mpr
  simp only [CleanTreeFactors.allZero, allZero, decide_eq_true_eq]
  change ((∀ q, x.1 ((Fintype.equivFin C).symm q) = 0) ∧
      ∀ node row, x.2 node row = 0) ↔
    ((∀ q, x.1 q = 0) ∧ ∀ node row, x.2 node row = 0)
  constructor
  · rintro ⟨hc, ha⟩
    refine ⟨fun q => ?_, ha⟩
    simpa only [Equiv.symm_apply_apply] using hc (Fintype.equivFin C q)
  · rintro ⟨hc, ha⟩
    exact ⟨fun q => hc ((Fintype.equivFin C).symm q), ha⟩

def rawLaw : FiniteDistribution (Raw (C := C) rows ids) :=
  FiniteDistribution.uniform (Raw (C := C) rows ids)

theorem rawLaw_reindex :
    (rawLaw (C := C) rows ids).pushforward (rawEquiv rows ids) =
      CleanTreeFactors.rawLaw (Fintype.card C) rows ids := by
  rw [CleanTreeFactors.rawLaw_uniform, rawLaw, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (Raw (C := C) rows ids) : ℝ) =
    1 / (Fintype.card (CleanTreeFactors.Raw (Fintype.card C) rows ids) : ℝ)
  rw [Fintype.card_congr (rawEquiv (C := C) rows ids)]

def shapeProbability (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) : ℝ :=
  ∏ j : CleanTreeFactors.Index branch n calls rows,
    1 / (shapeCardinality branch t
      (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows) j : ℝ)

theorem probability_allZero_eq_cleanTree :
    (rawLaw (C := C) rows ids).probability (allZero rows ids) =
      (CleanTreeFactors.rawLaw (Fintype.card C) rows ids).probability
        (CleanTreeFactors.allZero (Fintype.card C) rows ids) := by
  have h := congrArg
    (fun μ : FiniteDistribution (CleanTreeFactors.Raw (Fintype.card C) rows ids) =>
      μ.probability (CleanTreeFactors.allZero (Fintype.card C) rows ids))
    (rawLaw_reindex (C := C) rows ids)
  rw [FiniteDistribution.probability_pushforward] at h
  simpa only [allZero_rawEquiv] using h

theorem probability_allZero :
    (rawLaw (C := C) rows ids).probability (allZero rows ids) =
      shapeProbability branch n t (Fintype.card C) rows := by
  rw [probability_allZero_eq_cleanTree]
  exact CleanTreeFactors.probability_allZero (Fintype.card C) rows ids

theorem probability_allZero_pos :
    0 < (rawLaw (C := C) rows ids).probability (allZero rows ids) := by
  rw [probability_allZero_eq_cleanTree]
  exact CleanTreeFactors.probability_allZero_pos (Fintype.card C) rows ids

theorem probability_allZero_eq_of_card_eq {D : Type*} [Fintype D]
    (ids' : Slots branch n → Fin t → Nat) (hcard : Fintype.card C = Fintype.card D) :
    (rawLaw (C := C) rows ids).probability (allZero rows ids) =
      (rawLaw (C := D) rows ids').probability (allZero rows ids') := by
  rw [probability_allZero, probability_allZero, hcard]


variable {root : Nat} (repeats : Nat → Nat)
  (p : DescendantSpaces.Path branch root (n + 1))

theorem probability_wholeCalls :
    (rawLaw (C := WholeCutCalls.Index rows repeats p) rows ids).probability (allZero rows ids) =
      shapeProbability branch n t
        (rows (n + 1) + ∑ h ∈ Finset.Ioc (n + 1) root,
          (2 ^ rows h - 1) * ∏ k ∈ Finset.Ioc (n + 1) h, 2 * repeats k) rows := by
  rw [probability_allZero, WholeCutCalls.card_eq_formula]

theorem probability_wholeCalls_eq {ancestorBranch : Nat → Nat}
    (p' : DescendantSpaces.Path ancestorBranch root (n + 1))
    (ids' : Slots branch n → Fin t → Nat) :
    (rawLaw (C := WholeCutCalls.Index rows repeats p) rows ids).probability (allZero rows ids) =
      (rawLaw (C := WholeCutCalls.Index rows repeats p') rows ids').probability
        (allZero rows ids') := by
  apply probability_allZero_eq_of_card_eq rows ids ids'
  rw [WholeCutCalls.card_eq_formula, WholeCutCalls.card_eq_formula]


end
end PerfectCompleteness.CutChildCleanLaw



namespace PerfectCompleteness.UniformCleanSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning SelectedSources UniformLatent

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

abbrev ChildRaw (i : I) := Sum (D i) (UniformLatent.Raw (Ω i))

def childKernel (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))
    (i : I) (e : E i) (r : R i) : FiniteDistribution (ChildRaw (D := D) Ω i) :=
  projectedKernel (Ω i) (flag i) (nonprojected i) (e, r)

def childClean (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (i : I) (_ : E i) (_ : R i) : ChildRaw (D := D) Ω i → Bool :=
  projectedZero (Ω i) (zero i)

def childrenLaw (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i)) :
    FiniteDistribution ((i : I) → E i × (R i × ChildRaw (D := D) Ω i)) :=
  law (fun i => kernelJoint (μ i) (fun e =>
    kernelJoint (ν i) (childKernel Ω flag nonprojected i e)))

abbrev Record (i : I) := Sum (E i × (R i × ChildRaw (D := D) Ω i)) (R i)

def cleanRecord {i : I} : Record (D := D) Ω i → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

abbrev CleanIndices (record : (i : I) → Record (D := D) Ω i) :=
  {i : I // cleanRecord Ω (record i) = true}

def rowEvent
    (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (record : (i : I) → Record (D := D) Ω i)
    (i : I) (x : E i × (R i × ChildRaw (D := D) Ω i)) : Bool := by
  classical
  exact decide (childObservation (childClean (D := D) Ω zero i) x = record i)

def recordEvent
    (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (record : (i : I) → Record (D := D) Ω i) :
    ((i : I) → E i × (R i × ChildRaw (D := D) Ω i)) → Bool :=
  allEvent (rowEvent Ω zero record)

omit [∀ index, DecidableEq (D index)] in
theorem clean_source_law
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))
    (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (cardinality : (i : I) → J i → Nat)
    (same_cardinality : ∀ i s j, Fintype.card (Ω i s j) = cardinality i j)
    (record : (i : I) → Record (D := D) Ω i)
    (positive : 0 < (childrenLaw Ω μ ν flag nonprojected).probability
      (recordEvent (D := D) Ω zero record)) :
    ((childrenLaw Ω μ ν flag nonprojected).condition (recordEvent (D := D) Ω zero record)
      positive).pushforward (Γ := (i : CleanIndices Ω record) → E i.1)
        (fun x (i : CleanIndices Ω record) => (x i.1).1) =
      law (I := CleanIndices Ω record) (Ω := fun i : CleanIndices Ω record => E i.1)
        (fun i : CleanIndices Ω record => μ i.1) := by
  classical
  let P := fun i => kernelJoint (μ i) (fun e =>
    kernelJoint (ν i) (childKernel Ω flag nonprojected i e))
  let event := rowEvent Ω zero record
  have hpositive : 0 < (law P).probability (allEvent event) := positive
  apply selected_sources_conditioned (I := I)
    (Ω := fun i => E i × (R i × ChildRaw (D := D) Ω i)) P event hpositive
    (fun i => cleanRecord Ω (record i) = true)
    (fun _ x => x.1) (fun i => μ i.1)
  intro i
  have hr : ∃ r, record i.1 = Sum.inr r := by
    have hi := i.property
    cases hrec : record i.1 with
    | inl raw => simp [cleanRecord, hrec] at hi
    | inr r => exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hr
  have hevent : event i.1 =
      (fun x => decide (x.2.1 = r) && childClean (D := D) Ω zero i.1 x.1 x.2.1 x.2.2) := by
    funext x
    cases hclean : childClean (D := D) Ω zero i.1 x.1 x.2.1 x.2.2 <;>
      simp [event, rowEvent, hr, childObservation, hclean]
  have hp := coordinate_probability_positive P event hpositive i.1
  rw [hevent] at hp
  have hconst : ∀ e r, (childKernel Ω flag nonprojected i.1 e r).probability
      (childClean (D := D) Ω zero i.1 e r) =
      (flag i.1).weight true * ∏ j, 1 / (cardinality i.1 j : ℝ) := by
    intro e r
    exact probability_projectedKernel_zero_constant (Ω i.1) (flag i.1) (nonprojected i.1)
      (zero i.1) (cardinality i.1) (same_cardinality i.1) (e, r)
  simpa only [hevent] using
    designated_source_condition (μ i.1) (ν i.1) (childKernel Ω flag nonprojected i.1)
      (childClean (D := D) Ω zero i.1)
      ((flag i.1).weight true * ∏ j, 1 / (cardinality i.1 j : ℝ)) hconst r hp

end
end PerfectCompleteness.UniformCleanSources



namespace PerfectCompleteness.CleanSourceRecord

open scoped Classical
open SourceQuestionReconstruction

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Leaf : I → Type*} [∀ i, Fintype (Leaf i)] [∀ i, DecidableEq (Leaf i)]
  (designated : (i : I) → Leaf i) {m t : Nat}

abbrev Rest (i : I) := {leaf : Leaf i // leaf ≠ designated i} → SourceTuple m t

def assemble (i : I) (e : SourceTuple m t) (r : Rest designated (m := m) (t := t) i) :
    Leaf i → SourceTuple m t :=
  (Equiv.piSplitAt (designated i) (fun _ : Leaf i => SourceTuple m t)).symm (e, r)

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)] in
@[simp] theorem assemble_designated (i : I) (e : SourceTuple m t)
    (r : Rest designated (m := m) (t := t) i) :
    assemble designated i e r (designated i) = e := by
  simp [assemble, Equiv.piSplitAt]

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)] in
@[simp] theorem assemble_other (i : I) (e : SourceTuple m t)
    (r : Rest designated (m := m) (t := t) i) (leaf : {leaf : Leaf i // leaf ≠ designated i}) :
    assemble designated i e r leaf.val = r leaf := by
  simp [assemble, Equiv.piSplitAt, leaf.property]

variable {J D : I → Type*}
  [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (SourceTuple m t × Rest designated (m := m) (t := t) i) → J i → Type*)
  [∀ i q j, Fintype (Ω i q j)] [∀ i q j, Nonempty (Ω i q j)]
  [∀ i q j, DecidableEq (Ω i q j)]

abbrev Sample := (i : I) → SourceTuple m t ×
  (Rest designated (m := m) (t := t) i × UniformCleanSources.ChildRaw (D := D) Ω i)

abbrev Record := (i : I) → UniformCleanSources.Record (D := D) Ω i

def clean (record : Record (D := D) designated Ω) (i : I) : Prop :=
  UniformCleanSources.cleanRecord Ω (record i) = true

def sourceTree (x : Sample (D := D) designated Ω) : (i : I) → Leaf i → SourceTuple m t :=
  fun i => assemble designated i (x i).1 (x i).2.1

omit [∀ index, Fintype (J index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)]
  [∀ index seed coord, DecidableEq (Ω index seed coord)] in
omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)] in
@[simp] theorem sourceTree_designated (x : Sample (D := D) designated Ω) (i : I) :
    sourceTree designated Ω x i (designated i) = (x i).1 :=
  assemble_designated designated i _ _

def visible (record : Record (D := D) designated Ω) :
    Visible (E := SourceTuple m t) designated (clean designated Ω record) :=
  fun i leaf =>
    match hrecord : record i with
    | .inl x => assemble designated i x.1 x.2.1 leaf.val
    | .inr r => r ⟨leaf.val, by
        intro heq
        apply leaf.property
        exact ⟨by simp only [clean, hrecord, UniformCleanSources.cleanRecord], heq⟩⟩

def rawProjected (i : I) : UniformCleanSources.ChildRaw (D := D) Ω i → Bool
  | .inl _ => false
  | .inr _ => true

def projected (record : Record (D := D) designated Ω) (i : I) : Bool :=
  match record i with
  | .inl x => rawProjected designated Ω i x.2.2
  | .inr _ => true

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Leaf index)]
  [∀ index, DecidableEq (Leaf index)]
  [∀ index, Fintype (J index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)]
  [∀ index seed coord, DecidableEq (Ω index seed coord)] in
theorem clean_projected (record : Record (D := D) designated Ω) (i : I)
    (hc : clean designated Ω record i) : projected designated Ω record i = true := by
  cases hrecord : record i with
  | inl x => simp only [clean, hrecord, UniformCleanSources.cleanRecord, Bool.false_eq_true] at hc
  | inr r => simp only [projected, hrecord]

variable (zero : (i : I) → (q : SourceTuple m t × Rest designated (m := m) (t := t) i) →
  (j : J i) → Ω i q j)

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem observation_eq (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) (i : I) :
    SelectedSources.childObservation (UniformCleanSources.childClean (D := D) Ω zero i) (x i) =
      record i := by
  have hall : ∀ j, UniformCleanSources.rowEvent (D := D) Ω zero record j (x j) = true := by
    simpa only [UniformCleanSources.recordEvent, CleanConditioning.allEvent, decide_eq_true_eq] using hevent
  simpa only [UniformCleanSources.rowEvent, decide_eq_true_eq] using hall i

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem visible_eq_reveal (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    visible designated Ω record =
      reveal designated (clean designated Ω record) (sourceTree designated Ω x) := by
  funext i leaf
  have hi := observation_eq designated Ω zero record x hevent i
  cases hc : UniformCleanSources.childClean (D := D) Ω zero i (x i).1 (x i).2.1 (x i).2.2 with
  | false =>
      have hr : record i = .inl (x i) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false] using hi.symm
      dsimp only [visible, reveal, sourceTree]
      split
      · rename_i y hy
        have hyx : y = x i := Sum.inl.inj (hy.symm.trans hr)
        exact congrArg (fun z => assemble designated i z.1 z.2.1 leaf.val) hyx
      · rename_i r hy
        have hbad := hy.symm.trans hr
        cases hbad
  | true =>
      have hr : record i = .inr (x i).2.1 := by
        simpa only [SelectedSources.childObservation, hc, ite_true] using hi.symm
      have hn : leaf.val ≠ designated i := by
        intro heq
        apply leaf.property
        exact ⟨by simp only [clean, hr, UniformCleanSources.cleanRecord], heq⟩
      dsimp only [visible, reveal, sourceTree]
      split
      · rename_i y hy
        have hbad := hy.symm.trans hr
        cases hbad
      · rename_i r hy
        have hrx : r = (x i).2.1 := Sum.inr.inj (hy.symm.trans hr)
        exact (congrFun hrx ⟨leaf.val, hn⟩).trans
          (assemble_other designated i (x i).1 (x i).2.1 ⟨leaf.val, hn⟩).symm

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem projected_eq_raw (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    projected designated Ω record = fun i => rawProjected designated Ω i (x i).2.2 := by
  funext i
  have hi := observation_eq designated Ω zero record x hevent i
  cases hc : UniformCleanSources.childClean (D := D) Ω zero i (x i).1 (x i).2.1 (x i).2.2 with
  | false =>
      have hr : record i = .inl (x i) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false] using hi.symm
      simp only [projected, hr]
  | true =>
      have hr : record i = .inr (x i).2.1 := by
        simpa only [SelectedSources.childObservation, hc, ite_true] using hi.symm
      rw [projected, hr]
      cases hraw : (x i).2.2 with
      | inl d =>
          simp only [UniformCleanSources.childClean, UniformLatent.projectedZero,
            hraw, Bool.false_eq_true] at hc
      | inr raw => rfl

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem clean_projected_raw (record : Record (D := D) designated Ω)
    (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true)
    (i : I) (hc : clean designated Ω record i) :
    rawProjected designated Ω i (x i).2.2 = true :=
  (congrFun (projected_eq_raw designated Ω zero record x hevent) i).symm.trans
    (clean_projected designated Ω record i hc)

variable {v : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem reconstructLeft_eq (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    SourceQuestionReconstruction.reconstructLeft designated (clean designated Ω record)
      (v := v) (visible designated Ω record)
      (fun i k => ((x i.val).1 k).1) =
        fun i leaf => leftTuple (v := v) (sourceTree designated Ω x i leaf) := by
  rw [visible_eq_reveal designated Ω zero record x hevent]
  simpa only [sourceTree_designated] using
    SourceQuestionReconstruction.reconstructLeft_eq designated (clean designated Ω record)
      (v := v) (sourceTree designated Ω x)

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem reconstructRight_eq (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    SourceQuestionReconstruction.reconstructRight designated (clean designated Ω record) clauses
      (projected designated Ω record) (visible designated Ω record)
      (fun i k => SourceClause.occurrenceVariable clauses ((x i.val).1 k)) =
        fun i leaf => rightTuple clauses (rawProjected designated Ω i (x i).2.2)
          (sourceTree designated Ω x i leaf) := by
  rw [visible_eq_reveal designated Ω zero record x hevent]
  have h := SourceQuestionReconstruction.reconstructRight_eq designated (clean designated Ω record)
    clauses (projected designated Ω record) (clean_projected designated Ω record)
    (sourceTree designated Ω x)
  simpa only [sourceTree_designated, projected_eq_raw designated Ω zero record x hevent] using h

omit [DecidableEq I] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem reconstructRight_slots (record : Record (D := D) designated Ω) (x : Sample (D := D) designated Ω)
    (hevent : UniformCleanSources.recordEvent (D := D) Ω zero record x = true) :
    (fun i leaf k => SourceKeys.slot clauses
      (SourceQuestionReconstruction.reconstructRight designated (clean designated Ω record) clauses
        (projected designated Ω record) (visible designated Ω record)
        (fun j q => SourceClause.occurrenceVariable clauses ((x j.val).1 q)) i leaf k)) =
      fun i leaf k => SourceKeys.slot clauses
        (rightTuple clauses (rawProjected designated Ω i (x i).2.2)
          (sourceTree designated Ω x i leaf) k) := by
  rw [reconstructRight_eq designated Ω zero clauses record x hevent]

end
end PerfectCompleteness.CleanSourceRecord



namespace PerfectCompleteness.ProjectedCleanLaw

open UniqueGamesTheorem.Foundations.Games
open FiniteProduct ProjectedCardinality UniformCleanSources

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (branch : I → Nat → Nat) (t : I → Nat)
  (height : (i : I) → J i → Nat) (square : (i : I) → J i → Bool)
  (ids : (i : I) → (E i × R i) → (j : J i) →
    RecursiveSpaces.Slots (branch i) (height i j) → Fin (t i) → Nat)

abbrev treeFactors (i : I) (s : E i × R i) (j : J i) : Type :=
  Factor (square i j) (ids i s j)

def treeZeros (i : I) (s : E i × R i) (j : J i) :
    treeFactors branch t height square ids i s j :=
  factorZero (square i j) (ids i s j)

local notation "Ωtree" => treeFactors branch t height square ids
local notation "ztree" => treeZeros branch t height square ids

omit [∀ index, DecidableEq (D index)] in
theorem designated_source_law
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))
    (record : (i : I) → UniformCleanSources.Record (D := D) Ωtree i)
    (positive : 0 < (childrenLaw Ωtree μ ν flag nonprojected).probability
      (recordEvent (D := D) Ωtree ztree record)) :
    ((childrenLaw Ωtree μ ν flag nonprojected).condition (recordEvent (D := D) Ωtree ztree record)
      positive).pushforward (Γ := (i : CleanIndices Ωtree record) → E i.1)
        (fun x (i : CleanIndices Ωtree record) => (x i.1).1) =
      law (I := CleanIndices Ωtree record) (Ω := fun i : CleanIndices Ωtree record => E i.1)
        (fun i : CleanIndices Ωtree record => μ i.1) := by
  classical
  apply clean_source_law Ωtree μ ν flag nonprojected ztree
    (fun i => shapeCardinality (branch i) (t i) (height i) (square i)) _ record positive
  intro i s j
  exact factor_card_eq (square i j) (ids i s j) (fun _ _ => 0)

end
end PerfectCompleteness.ProjectedCleanLaw



namespace PerfectCompleteness.UniformCleanSoundness

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning SelectedSources UniformLatent UniformCleanSources
open FiniteConditioningBounds

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  {R J D : I → Type*}
  [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

abbrev Sample := (i : I) → E × (R i × ChildRaw (D := D) Ω i)
abbrev FullRecord := (i : I) → Record (D := D) Ω i

def observations (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (x : Sample (D := D) Ω) : FullRecord (D := D) Ω :=
  fun i => childObservation (childClean (D := D) Ω zero i) (x i)

omit [DecidableEq I] [Fintype E] [DecidableEq E]
  [∀ index, Fintype (R index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (J index)] [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem recordEvent_eq
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (record : FullRecord (D := D) Ω) :
    recordEvent (D := D) Ω zero record =
      (fun x => decide (observations (D := D) Ω zero x = record)) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [recordEvent, rowEvent, allEvent, decide_eq_true_eq,
    observations, funext_iff]

omit [DecidableEq I] [Fintype E] [DecidableEq E]
  [∀ index, Fintype (R index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (R index)] [∀ index, DecidableEq (J index)]
  [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem observed_clean_count
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (x : Sample (D := D) Ω) :
    Fintype.card (CleanIndices Ω (observations (D := D) Ω zero x)) =
      CleanCounting.cleanCount
        (fun i y => childClean (D := D) Ω zero i y.1 y.2.1 y.2.2) x := by
  classical
  change Fintype.card {i : I //
      cleanRecord Ω (observations (D := D) Ω zero x i) = true} = _
  rw [Fintype.card_subtype]
  unfold CleanCounting.cleanCount
  congr 1
  ext i
  cases h : childClean (D := D) Ω zero i (x i).1 (x i).2.1 (x i).2.2 <;>
    simp [observations, childObservation, cleanRecord, h]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

omit [∀ index, DecidableEq (D index)] in
theorem conditional_source_bound
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E × R i → FiniteDistribution (D i))
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (cardinality : (i : I) → J i → Nat)
    (same_cardinality : ∀ i s j, Fintype.card (Ω i s j) = cardinality i j)
    (record : FullRecord (D := D) Ω)
    (positive : 0 < (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).probability
      (recordEvent (D := D) Ω zero record))
    (event : Sample (D := D) Ω → Bool)
    (strategy : Strategy (CleanIndices Ω record → Q₁) (CleanIndices Ω record → Q₂)
      (CleanIndices Ω record → A₁) (CleanIndices Ω record → A₂))
    (inclusion : ∀ x, recordEvent (D := D) Ω zero record x = true → event x = true →
      (IndexedRepetition.game G (CleanIndices Ω record)).wins strategy
        (fun i => (x i.1).1) = true) :
    ((childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).condition
      (recordEvent (D := D) Ω zero record) positive).probability event ≤
        (G.repetition (Fintype.card (CleanIndices Ω record))).value := by
  apply conditioned_source_success
    (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected)
    (recordEvent (D := D) Ω zero record) event positive G
    (fun x (i : CleanIndices Ω record) => (x i.1).1) _ strategy inclusion
  exact clean_source_law Ω (fun _ => G.occurrences) ν flag nonprojected zero
    cardinality same_cardinality record positive

omit [∀ index, DecidableEq (D index)] in
theorem source_soundness
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E × R i → FiniteDistribution (D i))
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (cardinality : (i : I) → J i → Nat)
    (same_cardinality : ∀ i s j, Fintype.card (Ω i s j) = cardinality i j)
    (event : Sample (D := D) Ω → Bool) (a : ℝ)
    (repetition : ∀ n, (G.repetition n).value ≤ a ^ n)
    (strategies : (record : FullRecord (D := D) Ω) →
      Strategy (CleanIndices Ω record → Q₁) (CleanIndices Ω record → Q₂)
        (CleanIndices Ω record → A₁) (CleanIndices Ω record → A₂))
    (inclusion : ∀ record x, recordEvent (D := D) Ω zero record x = true → event x = true →
      (IndexedRepetition.game G (CleanIndices Ω record)).wins (strategies record)
        (fun i => (x i.1).1) = true) :
    (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).probability event ≤
      ∏ i : I, (1 - (1 - a) *
        ((flag i).weight true * ∏ j : J i, 1 / (cardinality i j : ℝ))) := by
  classical
  let P := fun i => kernelJoint G.occurrences (fun e =>
    kernelJoint (ν i) (childKernel Ω flag nonprojected i e))
  let clean := fun i (y : E × (R i × ChildRaw (D := D) Ω i)) =>
    childClean (D := D) Ω zero i y.1 y.2.1 y.2.2
  have conditional : ∀ record (positive : 0 < (law P).probability
      (fun x => decide (observations (D := D) Ω zero x = record))),
      ((law P).condition (fun x => decide (observations (D := D) Ω zero x = record))
        positive).probability event ≤ a ^ Fintype.card (CleanIndices Ω record) := by
    intro record positive
    have hp' : 0 < (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).probability
        (recordEvent (D := D) Ω zero record) := by
      simpa only [childrenLaw, P, recordEvent_eq] using positive
    have bound := (conditional_source_bound Ω G ν flag nonprojected zero cardinality
      same_cardinality record hp' event (strategies record) (inclusion record)).trans
        (repetition _)
    simpa only [childrenLaw, P, recordEvent_eq] using bound
  have h := independent_clean_bound P clean (observations (D := D) Ω zero)
    (fun record => Fintype.card (CleanIndices Ω record))
    (observed_clean_count Ω zero) event a conditional
  have hp (i : I) : (P i).probability (clean i) =
      (flag i).weight true * ∏ j : J i, 1 / (cardinality i j : ℝ) := by
    apply CleanCounting.kernel_clean_probability
      (fun _ => G.occurrences) ν (childKernel Ω flag nonprojected)
      (childClean (D := D) Ω zero)
      (fun i => (flag i).weight true * ∏ j : J i, 1 / (cardinality i j : ℝ)) _ i
    intro k e r
    exact probability_projectedKernel_zero_constant (Ω k) (flag k) (nonprojected k)
      (zero k) (cardinality k) (same_cardinality k) (e, r)
  change (law P).probability event ≤ _
  simpa only [hp] using h

end
end PerfectCompleteness.UniformCleanSoundness



namespace PerfectCompleteness.ProjectedCleanRate

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces ProjectedCardinality CleanTreeFactors UniformCleanSources

noncomputable section

def zeroProbability (branch : Nat → Nat) (height t calls : Nat) (rows : Nat → Nat) : ℝ :=
  ∏ j : CleanTreeFactors.Index branch height calls rows,
    1 / (shapeCardinality branch t
      (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows) j : ℝ)

theorem zeroProbability_positive (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) : 0 < zeroProbability branch height t calls rows :=
  shape_zero_probability_pos branch t
    (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows)

theorem zeroProbability_le_one (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) : zeroProbability branch height t calls rows ≤ 1 := by
  change (∏ j : CleanTreeFactors.Index branch height calls rows,
    1 / (shapeCardinality branch t
      (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows) j : ℝ)) ≤ 1
  rw [← CleanTreeFactors.probability_allZero calls rows
    (fun (_ : Slots branch height) (_ : Fin t) => 0)]
  exact FiniteDistribution.probability_le_one _ _

theorem raw_zero_probability (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) (ids : Slots branch height → Fin t → Nat) :
    (CleanTreeFactors.rawLaw calls rows ids).probability
      (CleanTreeFactors.allZero calls rows ids) =
        zeroProbability branch height t calls rows :=
  CleanTreeFactors.probability_allZero calls rows ids

def coefficient (L : Nat) (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) : ℝ :=
  zeroProbability branch height t calls rows / (48000 * (L : ℝ))

theorem coefficient_eq (L : Nat) (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) :
    coefficient L branch height t calls rows =
      (1 - (RepetitionRate.halfRate L : ℝ)) * zeroProbability branch height t calls rows := by
  rw [RepetitionRate.halfRate_cast]
  unfold coefficient
  ring

theorem coefficient_bounds {L : Nat} (hL : 0 < L) (branch : Nat → Nat)
    (height t calls : Nat) (rows : Nat → Nat) :
    0 < coefficient L branch height t calls rows ∧
      coefficient L branch height t calls rows ≤ 1 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℝ) < 48000 * L := by positivity
  have hp := zeroProbability_positive branch height t calls rows
  have hp1 := zeroProbability_le_one branch height t calls rows
  constructor
  · exact div_pos hp hden
  · apply (div_le_one hden).2
    linarith

def projectionDensity (cube : Nat) : ℝ := 1 / (cube : ℝ) ^ 2

theorem projectionDensity_bounds {cube : Nat} (hcube : 0 < cube) :
    0 ≤ projectionDensity cube ∧ projectionDensity cube ≤ 1 := by
  have hc : (1 : ℝ) ≤ cube := by exact_mod_cast hcube
  have hsq : (1 : ℝ) ≤ (cube : ℝ) ^ 2 := by nlinarith
  constructor
  · exact one_div_nonneg.mpr (sq_nonneg _)
  · exact (div_le_one (by positivity)).2 hsq

def projectionFlag (cube : Nat) (hcube : 0 < cube) : FiniteDistribution Bool :=
  RepetitionRate.bernoulli (projectionDensity cube)
    (projectionDensity_bounds hcube).1 (projectionDensity_bounds hcube).2

@[simp] theorem projectionFlag_true (cube : Nat) (hcube : 0 < cube) :
    (projectionFlag cube hcube).weight true = projectionDensity cube := by
  simp [projectionFlag, RepetitionRate.bernoulli]

theorem cube_product {L cube : Nat} (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) :
    (∏ _i : Fin (cube ^ 3),
      (1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
        (projectionDensity cube * zeroProbability branch height t calls rows))) =
      (1 - coefficient L branch height t calls rows / (cube : ℝ) ^ 2) ^ (cube ^ 3) := by
  have hbase : 1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
      (projectionDensity cube * zeroProbability branch height t calls rows) =
      1 - coefficient L branch height t calls rows / (cube : ℝ) ^ 2 := by
    rw [coefficient_eq]
    unfold projectionDensity
    ring
  simp only [hbase, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

section ActualLaw

variable {E : Type*} [Fintype E] [DecidableEq E]
  {cube : Nat} {R D : Fin (cube ^ 3) → Type*}
  [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
  [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
  (branch : Nat → Nat) (height t calls : Nat) (rows : Nat → Nat)
  (ids : (i : Fin (cube ^ 3)) → E × R i → Slots branch height → Fin t → Nat)

abbrev Factors (i : Fin (cube ^ 3)) (source : E × R i)
    (j : CleanTreeFactors.Index branch height calls rows) :=
  CleanTreeFactors.Factors calls rows (ids i source) j

def zeros (i : Fin (cube ^ 3)) (source : E × R i)
    (j : CleanTreeFactors.Index branch height calls rows) :
    Factors branch height t calls rows ids i source j :=
  factorZero (CleanTreeFactors.square calls rows j)
    (CleanTreeFactors.factorIds calls rows (ids i source) j)

local notation "Ω" => Factors branch height t calls rows ids
local notation "z" => zeros branch height t calls rows ids

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

omit [∀ index, DecidableEq (D index)] in
theorem bound_from_repetition {L : Nat} (hcube : 0 < cube)
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (repetition : ∀ k, (G.repetition k).value ≤ (RepetitionRate.halfRate L : ℝ) ^ k)
    (ν : (i : Fin (cube ^ 3)) → FiniteDistribution (R i))
    (nonprojected : (i : Fin (cube ^ 3)) → E × R i → FiniteDistribution (D i))
    (event : UniformCleanSoundness.Sample (D := D) Ω → Bool)
    (strategies : (record : UniformCleanSoundness.FullRecord (D := D) Ω) →
      Strategy (CleanIndices Ω record → Q₁) (CleanIndices Ω record → Q₂)
        (CleanIndices Ω record → A₁) (CleanIndices Ω record → A₂))
    (inclusion : ∀ record x, recordEvent (D := D) Ω z record x = true →
      event x = true →
      (IndexedRepetition.game G (CleanIndices Ω record)).wins (strategies record)
        (fun i => (x i.1).1) = true) :
    (childrenLaw Ω (fun _ => G.occurrences) ν (fun _ => projectionFlag cube hcube)
      nonprojected).probability event ≤
      (1 - coefficient L branch height t calls rows / (cube : ℝ) ^ 2) ^ (cube ^ 3) := by
  have bound := UniformCleanSoundness.source_soundness Ω G ν
    (fun _ => projectionFlag cube hcube) nonprojected z
    (fun _ => shapeCardinality branch t
      (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows))
    (fun i source j => factor_card_eq (CleanTreeFactors.square calls rows j)
      (CleanTreeFactors.factorIds calls rows (ids i source) j) (fun _ _ => 0))
    event (RepetitionRate.halfRate L : ℝ) repetition strategies inclusion
  calc
    _ ≤ ∏ _i : Fin (cube ^ 3),
        (1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
          (projectionDensity cube * zeroProbability branch height t calls rows)) := by
      simpa only [projectionFlag_true, zeroProbability] using bound
    _ = _ := cube_product branch height t calls rows

end ActualLaw

theorem exists_cube_errors_lt {L : Nat} (hL : 0 < L)
    (branch : Nat → Nat) (height t calls : Nat) (rows : Nat → Nat)
    {likelihood ε : ℝ} (hlikelihood : 0 ≤ likelihood) (hε : 0 < ε) :
    ∃ cube : Nat, 2 ≤ cube ∧
      Real.sqrt (likelihood ^ 2 / (cube : ℝ) ^ 3) / 2 < ε ∧
      Real.sqrt ((1 + likelihood ^ 2 / (cube : ℝ) ^ 4) ^ (cube ^ 3) - 1) / 2 < ε ∧
      2 * ((1 / (cube : ℝ) ^ 2) * likelihood / (1 - 1 / (cube : ℝ) ^ 2)) < ε ∧
      (1 - coefficient L branch height t calls rows / (cube : ℝ) ^ 2) ^ (cube ^ 3) < ε :=
  CubicErrorSchedule.exists_cube_errors_lt hlikelihood
    (coefficient_bounds hL branch height t calls rows).1
    (coefficient_bounds hL branch height t calls rows).2 hε

end
end PerfectCompleteness.ProjectedCleanRate

end OAI
