import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalPrefixWords
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionHierarchyWords

open MatrixMultiplication.Foundation ConditionalPrefixWords
open scoped BigOperators Classical

universe u v x y z p q

structure ReadableHierarchy (A : Type u) (X : Type x) (Y : Type y) (Z : Type z) where
  Label : ℕ → Type v
  fintypeLabel : ∀ n, Fintype (Label n)
  labels : ∀ n, A → Label n
  depth : ℕ
  pair : ℕ → ReaderPair
  x : A → X
  y : A → Y
  z : A → Z
  coordinates_injective : Function.Injective (fun a => (x a, y a, z a))
  readXYX : (n : ℕ) → pair n = .xy → LabelRecord Label n → X → Label n
  readXYY : (n : ℕ) → pair n = .xy → LabelRecord Label n → Y → Label n
  readXZX : (n : ℕ) → pair n = .xz → LabelRecord Label n → X → Label n
  readXZZ : (n : ℕ) → pair n = .xz → LabelRecord Label n → Z → Label n
  readYZY : (n : ℕ) → pair n = .yz → LabelRecord Label n → Y → Label n
  readYZZ : (n : ℕ) → pair n = .yz → LabelRecord Label n → Z → Label n
  readXYX_readable : ∀ n, n < depth → ∀ (hp : pair n = .xy) (a : A),
    readXYX n hp (labelRecordOf labels n a) (x a) = labels n a
  readXYY_readable : ∀ n, n < depth → ∀ (hp : pair n = .xy) (a : A),
    readXYY n hp (labelRecordOf labels n a) (y a) = labels n a
  readXZX_readable : ∀ n, n < depth → ∀ (hp : pair n = .xz) (a : A),
    readXZX n hp (labelRecordOf labels n a) (x a) = labels n a
  readXZZ_readable : ∀ n, n < depth → ∀ (hp : pair n = .xz) (a : A),
    readXZZ n hp (labelRecordOf labels n a) (z a) = labels n a
  readYZY_readable : ∀ n, n < depth → ∀ (hp : pair n = .yz) (a : A),
    readYZY n hp (labelRecordOf labels n a) (y a) = labels n a
  readYZZ_readable : ∀ n, n < depth → ∀ (hp : pair n = .yz) (a : A),
    readYZZ n hp (labelRecordOf labels n a) (z a) = labels n a

attribute [instance] ReadableHierarchy.fintypeLabel

variable {A : Type u} {X : Type x} {Y : Type y} {Z : Type z}
variable (H : ReadableHierarchy A X Y Z)
variable {Position : Type p} [Fintype Position]

def longX (word : Position → A) : Position → X := fun i => H.x (word i)
def longY (word : Position → A) : Position → Y := fun i => H.y (word i)
def longZ (word : Position → A) : Position → Z := fun i => H.z (word i)

omit [Fintype Position] in
theorem longCoordinates_injective : Function.Injective
    (fun word : Position → A => (longX H word, longY H word, longZ H word)) := by
  intro word other h
  funext i
  apply H.coordinates_injective
  exact Prod.ext (congrFun (congrArg Prod.fst h) i)
    (Prod.ext (congrFun (congrArg (fun q => q.2.1) h) i)
      (congrFun (congrArg (fun q => q.2.2) h) i))

variable [Fintype A] {Prefix : Type q} {counts : A → ℕ} {n t : ℕ}

def Represents (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (prior : Prefix) (u : Position → X) (v : Position → Y) (w : Position → Z)
    (word : Position → A) : Prop :=
  u = longX H word ∧ v = longY H word ∧ w = longZ H word ∧
    ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)

def eligible (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (prior : Prefix) (u : Position → X) (v : Position → Y) (w : Position → Z) : Prop :=
  ∃ word : Position → A, Represents H priorWord prior u v w word

def readXYX (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (own : Position → X) : Position → H.Label n :=
  fun i => H.readXYX n hp ((priorWord prior).val i) (own i)

theorem readXYX_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXYX H priorWord hp prior (longX H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXYX n hp ((priorWord prior).val i) (H.x (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXYX_readable n hn hp (word i)

def readXYY (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (own : Position → Y) : Position → H.Label n :=
  fun i => H.readXYY n hp ((priorWord prior).val i) (own i)

theorem readXYY_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXYY H priorWord hp prior (longY H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXYY n hp ((priorWord prior).val i) (H.y (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXYY_readable n hn hp (word i)

def readXZX (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (own : Position → X) : Position → H.Label n :=
  fun i => H.readXZX n hp ((priorWord prior).val i) (own i)

theorem readXZX_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXZX H priorWord hp prior (longX H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXZX n hp ((priorWord prior).val i) (H.x (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXZX_readable n hn hp (word i)

def readXZZ (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (own : Position → Z) : Position → H.Label n :=
  fun i => H.readXZZ n hp ((priorWord prior).val i) (own i)

theorem readXZZ_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXZZ H priorWord hp prior (longZ H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXZZ n hp ((priorWord prior).val i) (H.z (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXZZ_readable n hn hp (word i)

def readYZY (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (own : Position → Y) : Position → H.Label n :=
  fun i => H.readYZY n hp ((priorWord prior).val i) (own i)

theorem readYZY_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readYZY H priorWord hp prior (longY H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readYZY n hp ((priorWord prior).val i) (H.y (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readYZY_readable n hn hp (word i)

def readYZZ (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (own : Position → Z) : Position → H.Label n :=
  fun i => H.readYZZ n hp ((priorWord prior).val i) (own i)

theorem readYZZ_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readYZZ H priorWord hp prior (longZ H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readYZZ n hp ((priorWord prior).val i) (H.z (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readYZZ_readable n hn hp (word i)

theorem readable_XY
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (hn : n < H.depth) (h : eligible H priorWord prior u v w) :
    readXYX H priorWord hp prior u =
      readXYY H priorWord hp prior v := by
  obtain ⟨word, hu, hv, hw, hprior⟩ := h
  rw [hu, hv]
  rw [readXYX_on_original_word H priorWord hp prior word hn hprior,
    readXYY_on_original_word H priorWord hp prior word hn hprior]

theorem readable_XZ
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (hn : n < H.depth) (h : eligible H priorWord prior u v w) :
    readXZX H priorWord hp prior u =
      readXZZ H priorWord hp prior w := by
  obtain ⟨word, hu, hv, hw, hprior⟩ := h
  rw [hu, hw]
  rw [readXZX_on_original_word H priorWord hp prior word hn hprior,
    readXZZ_on_original_word H priorWord hp prior word hn hprior]

theorem readable_YZ
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (hn : n < H.depth) (h : eligible H priorWord prior u v w) :
    readYZY H priorWord hp prior v =
      readYZZ H priorWord hp prior w := by
  obtain ⟨word, hu, hv, hw, hprior⟩ := h
  rw [hv, hw]
  rw [readYZY_on_original_word H priorWord hp prior word hn hprior,
    readYZZ_on_original_word H priorWord hp prior word hn hprior]

theorem represented_word_unique
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z) {word other : Position → A}
    (hword : Represents H priorWord prior u v w word)
    (hother : Represents H priorWord prior u v w other) : word = other := by
  apply longCoordinates_injective H
  exact Prod.ext (hword.1.symm.trans hother.1)
    (Prod.ext (hword.2.1.symm.trans hother.2.1)
      (hword.2.2.1.symm.trans hother.2.2.1))

theorem eligible_appendCode_iff
    (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts H.labels n t))
    (u : Position → X) (v : Position → Y) (w : Position → Z) :
    eligible H id (appendCode old code) u v w ↔
      ∃ word : Position → A, Represents H id old u v w word ∧
        ((conditionalPoolEquivFin old).symm code).val =
          (fun i => H.labels n (word i)) := by
  constructor
  · rintro ⟨word, hu, hv, hw, hprior⟩
    refine ⟨word, ⟨hu, hv, hw, ?_⟩, ?_⟩
    · intro i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf H.labels n (word i), H.labels n (word i)) at hi
      exact congrArg Prod.fst hi
    · funext i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf H.labels n (word i), H.labels n (word i)) at hi
      exact congrArg Prod.snd hi
  · rintro ⟨word, ⟨hu, hv, hw, hprior⟩, hfine⟩
    refine ⟨word, hu, hv, hw, ?_⟩
    intro i
    change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
      (labelRecordOf H.labels n (word i), H.labels n (word i))
    exact Prod.ext (hprior i) (congrFun hfine i)

theorem represented_fine_eq
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z) {word other : Position → A}
    (hword : Represents H priorWord prior u v w word)
    (hother : Represents H priorWord prior u v w other) :
    (fun i => H.labels n (word i)) = (fun i => H.labels n (other i)) := by
  rw [represented_word_unique H priorWord prior u v w hword hother]

theorem eligible_appendCode_iff_of_represents
    (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts H.labels n t))
    (u : Position → X) (v : Position → Y) (w : Position → Z) (word : Position → A)
    (hword : Represents H id old u v w word) :
    eligible H id (appendCode old code) u v w ↔
      ((conditionalPoolEquivFin old).symm code).val = (fun i => H.labels n (word i)) := by
  rw [eligible_appendCode_iff]
  constructor
  · rintro ⟨other, hother, hfine⟩
    exact hfine.trans (represented_fine_eq H id old u v w hother hword)
  · intro hfine
    exact ⟨word, hword, hfine⟩

theorem root_eligible_iff
    (old : ExactPrefix counts H.labels 0 t Position)
    (u : Position → X) (v : Position → Y) (w : Position → Z) :
    eligible H id old u v w ↔ ∀ i, ∃ a : A,
      H.x a = u i ∧ H.y a = v i ∧ H.z a = w i := by
  constructor
  · rintro ⟨word, hu, hv, hw, _⟩ i
    refine ⟨word i, ?_, ?_, ?_⟩
    · exact (congrFun hu i).symm
    · exact (congrFun hv i).symm
    · exact (congrFun hw i).symm
  · intro h
    choose word hx hy hz using h
    refine ⟨word, ?_, ?_, ?_, ?_⟩
    · funext i
      exact (hx i).symm
    · funext i
      exact (hy i).symm
    · funext i
      exact (hz i).symm
    · intro i
      exact Subsingleton.elim _ _

def terminalWord (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position) :
    PopulationWords Position (fun a => t * counts a) := by
  let source := sourcePrefixEquiv counts H.labels H.depth t Position complete last
  refine ⟨source.val, ?_⟩
  intro a
  refine Eq.trans ?_ (source.property a)
  unfold wordPopulation
  exact congrArg
    (fun inst : Fintype {i : Position // source.val i = a} => @Fintype.card _ inst)
    (Subsingleton.elim _ _)

theorem terminalWord_record
    (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position) (i : Position) :
    labelRecordOf H.labels H.depth ((terminalWord H complete last).val i) = last.val i :=
  sourceSymbol_record last i

theorem terminalWord_of_represents
    (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (word : Position → A) (hword : Represents H id last u v w word) :
    (terminalWord H complete last).val = word := by
  funext i
  exact (sourceSymbol_eq_iff complete last i (word i)).2 (hword.2.2.2 i)

theorem terminal_eligible_iff
    (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position)
    (u : Position → X) (v : Position → Y) (w : Position → Z) :
    eligible H id last u v w ↔
      u = longX H (terminalWord H complete last).val ∧
      v = longY H (terminalWord H complete last).val ∧
      w = longZ H (terminalWord H complete last).val := by
  constructor
  · rintro ⟨word, hword⟩
    rw [terminalWord_of_represents H complete last u v w word hword]
    exact ⟨hword.1, hword.2.1, hword.2.2.1⟩
  · rintro ⟨hu, hv, hw⟩
    refine ⟨(terminalWord H complete last).val, hu, hv, hw, ?_⟩
    intro i
    exact (terminalWord_record H complete last i).symm

end MatrixMultiplication.CompletionHierarchyWords

end

end OAI
