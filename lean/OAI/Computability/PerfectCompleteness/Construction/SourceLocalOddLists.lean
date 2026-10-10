import OAI.Computability.PerfectCompleteness.Foundations.OddListExtraction
import OAI.Computability.PerfectCompleteness.Foundations.SourceOddListsLemmas
import OAI.Computability.PerfectCompleteness.Repetition.RepetitionRateLemmas

namespace OAI

section

namespace PerfectCompleteness.SourceLocalOddLists

open scoped Classical
open PointwiseSpaces TreeSourceSpaces SourceAnswerEquiv
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

noncomputable section

variable {branch : Nat → Nat} {h t v m s : Nat}

abbrev Form (slots : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot) :=
  H slots →ₗ[F2] H slots →ₗ[F2] F2

def leafSupport (slots : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot)
    (F : Form slots) (leaf : RecursiveSpaces.Slots branch h) : Finset (LeafDomain slots leaf) :=
  OddLists.support (fun a => F
    (OddListExtraction.atom (H slots) (fun x => x leaf)
      (OddListExtraction.source_leaf_indicator_mem slots leaf) a)
    (OddListExtraction.atom (H slots) (fun x => x leaf)
      (OddListExtraction.source_leaf_indicator_mem slots leaf) a))

def extract (positive : 0 < s)
    (slots : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot)
    (F : Form slots) (leaf : RecursiveSpaces.Slots branch h) (fallback : LeafDomain slots leaf) :
    OddLists.OddList s (LeafDomain slots leaf) :=
  OddLists.OddList.extract positive fallback (leafSupport slots F leaf)

theorem extract_accepts (positive : 0 < s)
    {slots projected : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot}
    (p : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))
    (leaf : RecursiveSpaces.Slots branch h) (F : Form slots) (F' : Form projected)
    (z : Module.Dual F2 (squareSpace (H slots)))
    (hform : F = OddListExtraction.multiplicationForm (H slots) z)
    (hone : (1 : Domain slots → F2) ∈ squareSpace (H slots))
    (hnorm : z ⟨1, hone⟩ = 1) (hrank : OddListExtraction.formRank (H slots) F ≤ s)
    (hagree : ∀ f g, F' f g = OddListExtraction.multiplicationForm (H slots) z
      (HPullback p f) (HPullback p g))
    (leftFallback : LeafDomain slots leaf) (rightFallback : LeafDomain projected leaf) :
    OddLists.OddList.map (MixedSupport.projectionMap (p leaf))
      (extract positive slots F leaf leftFallback) =
      extract positive projected F' leaf rightFallback := by
  have hleft : Odd (leafSupport slots F leaf).card ∧ (leafSupport slots F leaf).card ≤ s := by
    rw [hform] at hrank ⊢
    exact (OddListExtraction.extractedList (H slots) (fun x => x leaf)
      (OddListExtraction.source_leaf_indicator_mem slots leaf) z hone hnorm s hrank).property
  have hsupport : leafSupport projected F' leaf =
      OddLists.parityPushforward (MixedSupport.projectionMap (p leaf)) (leafSupport slots F leaf) := by
    rw [hform]
    exact OddListExtraction.source_projected_support p leaf z F' hagree
  have hright : Odd (leafSupport projected F' leaf).card ∧
      (leafSupport projected F' leaf).card ≤ s := by
    rw [hsupport]
    exact ⟨OddLists.parityPushforward_odd _ _ hleft.1,
      (OddLists.parityPushforward_card_le _ _).trans hleft.2⟩
  apply Subtype.ext
  rw [OddLists.OddList.map_val]
  change OddLists.parityPushforward (MixedSupport.projectionMap (p leaf))
      (OddLists.OddList.extract positive leftFallback (leafSupport slots F leaf)).val =
    (OddLists.OddList.extract positive rightFallback (leafSupport projected F' leaf)).val
  rw [OddLists.OddList.extract_valid positive leftFallback _ hleft,
    OddLists.OddList.extract_valid positive rightFallback _ hright]
  exact hsupport.symm

private theorem map_eq_of_map_eq {A B : Type*} {s : Nat}
    {f₁ f₂ : Fintype B} {d₁ d₂ : DecidableEq B}
    (π : A → B) (L : OddLists.OddList s A) (R : OddLists.OddList s B)
    (accepted : @OddLists.OddList.map A B s f₁ d₁ π L = R) :
    @OddLists.OddList.map A B s f₂ d₂ π L = R := by
  have hf : f₁ = f₂ := Subsingleton.elim _ _
  cases hf
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact accepted

variable (clauses : Fin m → SourceClause.NormalizedClause v)

abbrev LeftQuestions := RecursiveSpaces.Slots branch h → Fin t → Fin m
abbrev RightQuestions := RecursiveSpaces.Slots branch h → Fin t → Fin v
abbrev Occurrences := RecursiveSpaces.Slots branch h → SourceOddLists.Occurrences m t

abbrev LeftForms := (q : LeftQuestions (branch := branch) (h := h) (t := t) (m := m)) →
  Form (leftTreeSlots clauses q)

abbrev RightForms := (q : RightQuestions (branch := branch) (h := h) (t := t) (v := v)) →
  Form (rightTreeSlots clauses q)

def leftResponse (positive : 0 < s) (forms : LeftForms (branch := branch) (h := h) (t := t) clauses)
    (q : LeftQuestions (branch := branch) (h := h) (t := t) (m := m))
    (leaf : RecursiveSpaces.Slots branch h) : OddLists.OddList s (SourceOddLists.LeftLabels t) :=
  encodeOddList clauses (q leaf)
    (extract positive (leftTreeSlots clauses q) (forms q) leaf
      ((leftEquiv clauses (q leaf)).symm (fun _ => 0)))

def rightResponse (positive : 0 < s) (forms : RightForms (branch := branch) (h := h) (t := t) clauses)
    (q : RightQuestions (branch := branch) (h := h) (t := t) (v := v))
    (leaf : RecursiveSpaces.Slots branch h) : OddLists.OddList s (SourceOddLists.RightLabels t) :=
  extract positive (rightTreeSlots clauses q) (forms q) leaf (fun _ => false)

def treeProjection (e : Occurrences (branch := branch) (h := h) (m := m) (t := t)) :
    ∀ leaf k, MixedSupport.Projection
      (leftTreeSlots clauses (fun j => SourceOddLists.left (e j)) leaf k)
      (rightTreeSlots clauses (fun j => SourceOddLists.right clauses (e j)) leaf k) :=
  fun leaf => slotProjection clauses (e leaf)

section Clean

variable (clean : RecursiveSpaces.Slots branch h → Prop)

abbrev CleanLeaves := {leaf : RecursiveSpaces.Slots branch h // clean leaf}

def fill {Q : Type*} (background : RecursiveSpaces.Slots branch h → Q)
    (q : CleanLeaves clean → Q) : RecursiveSpaces.Slots branch h → Q :=
  fun leaf => if hc : clean leaf then q ⟨leaf, hc⟩ else background leaf

@[simp] theorem fill_clean {Q : Type*} (background : RecursiveSpaces.Slots branch h → Q)
    (q : CleanLeaves clean → Q) (leaf : CleanLeaves clean) :
    fill clean background q leaf.val = q leaf := by
  simp only [fill, dite_eq_left leaf.property]

theorem fill_comp {Q R : Type*} (background : RecursiveSpaces.Slots branch h → Q)
    (q : CleanLeaves clean → Q) (f : Q → R) :
    fill clean (fun leaf => f (background leaf)) (fun leaf => f (q leaf)) =
      fun leaf => f (fill clean background q leaf) := by
  funext leaf
  by_cases hc : clean leaf
  · simp only [fill, dite_eq_left hc]
  · simp only [fill, dite_eq_right hc]

variable (background : Occurrences (branch := branch) (h := h) (m := m) (t := t))

def strategy (positive : 0 < s) (leftForms : LeftForms (branch := branch) (h := h) (t := t) clauses) (rightForms : RightForms (branch := branch) (h := h) (t := t) clauses) :
    Strategy (CleanLeaves clean → Fin t → Fin m) (CleanLeaves clean → Fin t → Fin v)
      (CleanLeaves clean → OddLists.OddList s (SourceOddLists.LeftLabels t))
      (CleanLeaves clean → OddLists.OddList s (SourceOddLists.RightLabels t)) :=
  (fun q leaf => leftResponse clauses positive leftForms
      (fill clean (fun j => SourceOddLists.left (background j)) q) leaf.val,
   fun q leaf => rightResponse clauses positive rightForms
      (fill clean (fun j => SourceOddLists.right clauses (background j)) q) leaf.val)

theorem strategy_wins [NeZero m] (positive : 0 < s)
    (leftForms : LeftForms (branch := branch) (h := h) (t := t) clauses) (rightForms : RightForms (branch := branch) (h := h) (t := t) clauses)
    (e : CleanLeaves clean → SourceOddLists.Occurrences m t)
    (z : Module.Dual F2 (squareSpace
      (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j))))))
    (hform : leftForms (fun j => SourceOddLists.left (fill clean background e j)) =
      OddListExtraction.multiplicationForm
        (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j)))) z)
    (hone :
      (1 : Domain (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j))) → F2) ∈
      squareSpace (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j)))))
    (hnorm : z ⟨1, hone⟩ = 1)
    (hrank : OddListExtraction.formRank
      (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j))))
      (leftForms (fun j => SourceOddLists.left (fill clean background e j))) ≤ s)
    (hagree : ∀ f g,
      rightForms (fun j => SourceOddLists.right clauses (fill clean background e j)) f g =
      OddListExtraction.multiplicationForm
        (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j)))) z
        (HPullback (treeProjection clauses (fill clean background e)) f)
        (HPullback (treeProjection clauses (fill clean background e)) g)) :
    (IndexedRepetition.game (SourceOddLists.game s clauses t) (CleanLeaves clean)).wins
      (strategy clauses clean background positive leftForms rightForms) e = true := by
  simp only [OccurrenceGame.wins, IndexedRepetition.game, SourceOddLists.game,
    OddListGame.game, OccurrenceGame.ofProjection, strategy, decide_eq_true_eq]
  intro leaf
  rw [fill_comp clean background e SourceOddLists.left,
    fill_comp clean background e (SourceOddLists.right clauses)]
  let full : Occurrences (branch := branch) (h := h) (m := m) (t := t) :=
    fill clean background e
  let qL : LeftQuestions (branch := branch) (h := h) (t := t) (m := m) :=
    fun j => SourceOddLists.left (full j)
  let qR : RightQuestions (branch := branch) (h := h) (t := t) (v := v) :=
    fun j => SourceOddLists.right clauses (full j)
  let slotsL : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot :=
    leftTreeSlots (branch := branch) (n := h) clauses qL
  let slotsR : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot :=
    rightTreeSlots (branch := branch) (n := h) clauses qR
  let L : OddLists.OddList s (LeftDomain clauses (SourceOddLists.left (full leaf.val))) :=
    extract (branch := branch) (h := h) (t := t) positive slotsL (leftForms qL) leaf.val
      ((leftEquiv clauses (SourceOddLists.left (full leaf.val))).symm (fun _ => 0))
  let R : OddLists.OddList s (RightDomain clauses (SourceOddLists.right clauses (full leaf.val))) :=
    extract (branch := branch) (h := h) (t := t) positive slotsR (rightForms qR) leaf.val
      (fun _ => false)
  have hraw := extract_accepts (branch := branch) (h := h) (t := t)
      (slots := slotsL) (projected := slotsR) positive
      (treeProjection (branch := branch) (h := h) (t := t) clauses full)
      leaf.val (leftForms qL) (rightForms qR) z hform hone hnorm hrank hagree
      ((leftEquiv clauses (SourceOddLists.left (full leaf.val))).symm (fun _ => 0))
      (fun _ => false)
  have hnative : OddLists.OddList.map (actualProjection clauses (full leaf.val)) L = R :=
    map_eq_of_map_eq _ L R hraw
  have haccept := encodeOddList_accepted clauses (full leaf.val) L R hnative
  rw [← fill_clean clean background e leaf]
  change OddLists.OddList.map (SourceOddLists.projection clauses (full leaf.val))
      (encodeOddList clauses (SourceOddLists.left (full leaf.val)) L) = R
  exact haccept

end Clean

end
end PerfectCompleteness.SourceLocalOddLists

end

end OAI
