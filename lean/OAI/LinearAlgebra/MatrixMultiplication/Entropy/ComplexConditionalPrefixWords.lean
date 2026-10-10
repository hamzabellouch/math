import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexStageHierarchyResources

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.ConditionalPrefixWords

open LabelHierarchyCounts StageHierarchyResources
open scoped BigOperators

universe u v w

local instance (priority := low) {B : Type*} : DecidableEq B := Classical.decEq B

instance labelRecordZero_subsingleton {Label : ℕ → Type v} :
    Subsingleton (LabelRecord Label 0) := by
  change Subsingleton PUnit
  infer_instance

private theorem population_fst {B C Position : Type*}
    [Fintype B] [Fintype C] [Fintype Position]
    (word : Position → B × C) (b : B) :
    wordPopulation (fun i => (word i).1) b = ∑ c, wordPopulation word (b, c) := by
  calc
    wordPopulation (fun i => (word i).1) b =
        ∑ c, wordPopulation (fun i : {i // (word i).1 = b} => (word i.val).2) c :=
      (wordPopulation_sum _).symm
    _ = ∑ c, Fintype.card {i // (word i).1 = b ∧ (word i).2 = c} := by
      apply Finset.sum_congr rfl
      intro c hc
      exact wordPopulation_fiber (fun i => (word i).1) (fun i => (word i).2) b c
    _ = ∑ c, wordPopulation word (b, c) := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [wordPopulation, Prod.ext_iff]

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

abbrev ExactPrefix (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (Position : Type w) [Fintype Position] :=
  PopulationWords Position (sourcePrefixCounts (fun a => t * counts a) labels n)

variable {Position : Type w} [Fintype Position]
variable {counts : A → ℕ} {labels : ∀ n, A → Label n} {n t : ℕ}

abbrev conditionalPool (old : ExactPrefix counts labels n t Position) :=
  ConditionalWords old.val
    (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))

def conditionalFinset (old : ExactPrefix counts labels n t Position) :
    Finset (Position → Label n) :=
  Finset.univ.filter (fun fine => ∀ r s,
    Fintype.card {i // old.val i = r ∧ fine i = s} =
      sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))

@[simp] theorem mem_conditionalFinset (old : ExactPrefix counts labels n t Position)
    (fine : Position → Label n) :
    fine ∈ conditionalFinset old ↔ ∀ r s,
      Fintype.card {i // old.val i = r ∧ fine i = s} =
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s) := by
  simp only [conditionalFinset, Finset.mem_filter, Finset.mem_univ, true_and]

def conditionalFinsetEquiv (old : ExactPrefix counts labels n t Position) :
    ↥(conditionalFinset old) ≃ conditionalPool old :=
  Equiv.subtypeEquivRight (fun fine => mem_conditionalFinset old fine)

theorem conditionalPool_card (old : ExactPrefix counts labels n t Position) :
    Fintype.card (conditionalPool old) = stageRefinementCount counts labels n t :=
  stageConditionalWords_card counts labels n t old.val old.property

theorem conditionalFinset_card (old : ExactPrefix counts labels n t Position) :
    (conditionalFinset old).card = stageRefinementCount counts labels n t :=
  stageConditionalPool_card counts labels n t old.val old.property

def conditionalFinsetEquivFin (old : ExactPrefix counts labels n t Position) :
    ↥(conditionalFinset old) ≃ Fin (stageRefinementCount counts labels n t) :=
  LabelHierarchySeparation.poolEnumeration
    (fun previous : ExactPrefix counts labels n t Position => conditionalFinset previous)
    (stageRefinementCount counts labels n t) (fun previous => conditionalFinset_card previous) old

def conditionalPoolEquivFin (old : ExactPrefix counts labels n t Position) :
    conditionalPool old ≃ Fin (stageRefinementCount counts labels n t) :=
  (conditionalFinsetEquiv old).symm.trans (conditionalFinsetEquivFin old)

@[simp] theorem decodedFine_eq_geometryDecode (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    ((conditionalPoolEquivFin old).symm code).val =
      ((LabelHierarchySeparation.poolEnumeration
        (fun previous : ExactPrefix counts labels n t Position => conditionalFinset previous)
        (stageRefinementCount counts labels n t)
        (fun previous => conditionalFinset_card previous) old).symm code).val := rfl

def appendPrefix (old : ExactPrefix counts labels n t Position) (fine : conditionalPool old) :
    ExactPrefix counts labels (n + 1) t Position := by
  classical
  refine ⟨fun i => (old.val i, fine.val i), ?_⟩
  rintro ⟨r, s⟩
  refine Eq.trans ?_ (fine.property r s)
  unfold wordPopulation
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => Prod.ext_iff)

omit [∀ n, Fintype (Label n)] in
@[simp] theorem appendPrefix_val (old : ExactPrefix counts labels n t Position)
    (fine : conditionalPool old) (i : Position) :
    (appendPrefix old fine).val i = (old.val i, fine.val i) := rfl

def oldPrefix (next : ExactPrefix counts labels (n + 1) t Position) :
    ExactPrefix counts labels n t Position := by
  classical
  refine ⟨fun i => (next.val i).1, ?_⟩
  intro r
  calc
    wordPopulation (fun i => (next.val i).1) r =
        ∑ s : Label n, wordPopulation next.val (r, s) := by
      have h := population_fst next.val r
      refine h.trans ?_
      apply Finset.sum_congr rfl
      intro s hs
      unfold wordPopulation
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    _ = ∑ s : Label n,
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact next.property (r, s)
    _ = sourcePrefixCounts (fun a => t * counts a) labels n r :=
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n r).symm

@[simp] theorem oldPrefix_val (next : ExactPrefix counts labels (n + 1) t Position)
    (i : Position) : (oldPrefix next).val i = (next.val i).1 := rfl

def finePrefix (next : ExactPrefix counts labels (n + 1) t Position) :
    conditionalPool (oldPrefix next) := by
  classical
  refine ⟨fun i => (next.val i).2, ?_⟩
  intro r s
  refine Eq.trans ?_ (next.property (r, s))
  unfold wordPopulation
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => by
    change ((next.val i).1 = r ∧ (next.val i).2 = s) ↔ next.val i = (r, s)
    constructor
    · rintro ⟨hfst, hsnd⟩
      exact Prod.ext hfst hsnd
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)

@[simp] theorem finePrefix_val (next : ExactPrefix counts labels (n + 1) t Position)
    (i : Position) : (finePrefix next).val i = (next.val i).2 := rfl

@[simp] theorem oldPrefix_appendPrefix (old : ExactPrefix counts labels n t Position)
    (fine : conditionalPool old) : oldPrefix (appendPrefix old fine) = old := by
  apply Subtype.ext
  rfl

def nextPrefixSigmaEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (Position : Type w) [Fintype Position] :
    ExactPrefix counts labels (n + 1) t Position ≃
      Σ old : ExactPrefix counts labels n t Position, conditionalPool old where
  toFun next := ⟨oldPrefix next, finePrefix next⟩
  invFun p := appendPrefix p.1 p.2
  left_inv next := by
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    rintro ⟨⟨old, ho⟩, ⟨fine, hf⟩⟩
    rfl

def nextPrefixEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (Position : Type w) [Fintype Position] :
    ExactPrefix counts labels (n + 1) t Position ≃
      ExactPrefix counts labels n t Position × Fin (stageRefinementCount counts labels n t) :=
  (nextPrefixSigmaEquiv counts labels n t Position).trans
    (Equiv.sigmaEquivProdOfEquiv (fun old => conditionalPoolEquivFin old))

def appendCode (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    ExactPrefix counts labels (n + 1) t Position :=
  appendPrefix old ((conditionalPoolEquivFin old).symm code)

@[simp] theorem appendCode_val (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) (i : Position) :
    (appendCode old code).val i =
      (old.val i, ((conditionalPoolEquivFin old).symm code).val i) := rfl

@[simp] theorem nextPrefixEquiv_symm_apply
    (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    (nextPrefixEquiv counts labels n t Position).symm (old, code) = appendCode old code := rfl

@[simp] theorem nextPrefixEquiv_appendCode
    (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    nextPrefixEquiv counts labels n t Position (appendCode old code) = (old, code) :=
  (nextPrefixEquiv counts labels n t Position).apply_symm_apply (old, code)

theorem appendCode_injective : Function.Injective
    (fun p : ExactPrefix counts labels n t Position × Fin (stageRefinementCount counts labels n t) =>
      appendCode p.1 p.2) :=
  (nextPrefixEquiv counts labels n t Position).symm.injective

theorem appendCode_surjective : Function.Surjective
    (fun p : ExactPrefix counts labels n t Position × Fin (stageRefinementCount counts labels n t) =>
      appendCode p.1 p.2) :=
  (nextPrefixEquiv counts labels n t Position).symm.surjective

theorem decodedFine_mem_conditionalFinset (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    ((conditionalPoolEquivFin old).symm code).val ∈ conditionalFinset old :=
  (mem_conditionalFinset old _).2 ((conditionalPoolEquivFin old).symm code).property

section Root

omit [∀ n, Fintype (Label n)]

private theorem rootPopulation (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (r : LabelRecord Label 0) :
    sourcePrefixCounts (fun a => t * counts a) labels 0 r = ∑ a, t * counts a := by
  cases r
  unfold sourcePrefixCounts pushforwardCounts
  apply Finset.sum_congr rfl
  intro a ha
  exact ite_eq_left (Subsingleton.elim _ _)

def rootPrefixWord (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (Position : Type w) [Fintype Position]
    (hN : Fintype.card Position = ∑ a, t * counts a) :
    ExactPrefix counts labels 0 t Position := by
  classical
  refine ⟨fun _ => PUnit.unit, ?_⟩
  intro r
  cases r
  calc
    _ = Fintype.card Position := by
      unfold wordPopulation
      exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => rfl))
    _ = ∑ a, t * counts a := hN
    _ = sourcePrefixCounts (fun a => t * counts a) labels 0 PUnit.unit :=
      (rootPopulation counts labels t PUnit.unit).symm

@[simp] theorem rootPrefixWord_val (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (hN : Fintype.card Position = ∑ a, t * counts a) (i : Position) :
    (rootPrefixWord counts labels t Position hN).val i = PUnit.unit := rfl

def rootPrefixEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (Position : Type w) [Fintype Position]
    (hN : Fintype.card Position = ∑ a, t * counts a) :
    ExactPrefix counts labels 0 t Position ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := rootPrefixWord counts labels t Position hN
  left_inv word := by
    apply Subtype.ext
    funext i
    exact Subsingleton.elim _ _
  right_inv point := by cases point; rfl

end Root

section Terminal

omit [∀ n, Fintype (Label n)]

variable {depth : ℕ}

theorem prefixSymbol_in_source_range (word : ExactPrefix counts labels depth t Position)
    (i : Position) : ∃ a : A, labelRecordOf labels depth a = word.val i := by
  by_contra hnone
  have hnot : ∀ a : A, labelRecordOf labels depth a ≠ word.val i := not_exists.mp hnone
  have hzero : sourcePrefixCounts (fun a => t * counts a) labels depth (word.val i) = 0 := by
    simp [sourcePrefixCounts, pushforwardCounts, hnot]
  have hpos : 0 < wordPopulation word.val (word.val i) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  rw [word.property (word.val i)] at hpos
  exact (Nat.ne_of_gt hpos) hzero

def sourceSymbol (word : ExactPrefix counts labels depth t Position) (i : Position) : A :=
  Classical.choose (prefixSymbol_in_source_range word i)

@[simp] theorem sourceSymbol_record (word : ExactPrefix counts labels depth t Position)
    (i : Position) : labelRecordOf labels depth (sourceSymbol word i) = word.val i :=
  Classical.choose_spec (prefixSymbol_in_source_range word i)

theorem sourceSymbol_eq_iff
    (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) (i : Position) (a : A) :
    sourceSymbol word i = a ↔ word.val i = labelRecordOf labels depth a := by
  constructor
  · intro h
    rw [← sourceSymbol_record word i, h]
  · intro h
    exact hinjective ((sourceSymbol_record word i).trans h)

theorem sourceSymbol_grade {Grade : Type*} (grade : A → Grade)
    (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) (i : Position) (a : A)
    (hrecord : labelRecordOf labels depth a = word.val i) :
    grade (sourceSymbol word i) = grade a :=
  congrArg grade ((sourceSymbol_eq_iff hinjective word i a).2 hrecord.symm)

def decodeSourceWord (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) :
    PopulationWords Position (fun a => t * counts a) := by
  refine ⟨fun i => sourceSymbol word i, ?_⟩
  intro a
  calc
    wordPopulation (fun i => sourceSymbol word i) a =
        wordPopulation word.val (labelRecordOf labels depth a) :=
      Fintype.card_congr (Equiv.subtypeEquivRight
        (fun i => sourceSymbol_eq_iff hinjective word i a))
    _ = sourcePrefixCounts (fun a => t * counts a) labels depth (labelRecordOf labels depth a) :=
      word.property _
    _ = t * counts a := pushforwardCounts_apply (fun a => t * counts a)
      (labelRecordOf labels depth) hinjective a

def encodeSourceWord (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth t : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) :
    ExactPrefix counts labels depth t Position := by
  refine ⟨fun i => labelRecordOf labels depth (word.val i), ?_⟩
  intro r
  by_cases hr : ∃ a : A, labelRecordOf labels depth a = r
  · obtain ⟨a, rfl⟩ := hr
    calc
      wordPopulation (fun i => labelRecordOf labels depth (word.val i))
          (labelRecordOf labels depth a) = wordPopulation word.val a := by
        simp only [wordPopulation, hinjective.eq_iff]
      _ = t * counts a := word.property a
      _ = sourcePrefixCounts (fun a => t * counts a) labels depth (labelRecordOf labels depth a) :=
        (pushforwardCounts_apply (fun a => t * counts a)
          (labelRecordOf labels depth) hinjective a).symm
  · have hnot : ∀ a : A, labelRecordOf labels depth a ≠ r := not_exists.mp hr
    simp [wordPopulation, sourcePrefixCounts, pushforwardCounts, hnot]

@[simp] theorem encodeSourceWord_val (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) (i : Position) :
    (encodeSourceWord counts labels depth t hinjective word).val i =
      labelRecordOf labels depth (word.val i) := rfl

@[simp] theorem sourceSymbol_encodeSourceWord (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) (i : Position) :
    sourceSymbol (encodeSourceWord counts labels depth t hinjective word) i = word.val i :=
  hinjective (sourceSymbol_record (encodeSourceWord counts labels depth t hinjective word) i)

def sourcePrefixEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth t : ℕ)
    (Position : Type w) [Fintype Position]
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    ExactPrefix counts labels depth t Position ≃ PopulationWords Position (fun a => t * counts a) where
  toFun word := decodeSourceWord hinjective word
  invFun word := encodeSourceWord counts labels depth t hinjective word
  left_inv word := by
    apply Subtype.ext
    funext i
    exact sourceSymbol_record word i
  right_inv word := by
    apply Subtype.ext
    funext i
    exact sourceSymbol_encodeSourceWord counts labels depth t hinjective word i

@[simp] theorem sourcePrefixEquiv_apply_val (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) (i : Position) :
    (sourcePrefixEquiv counts labels depth t Position hinjective word).val i =
      sourceSymbol word i := rfl

@[simp] theorem sourcePrefixEquiv_symm_val (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) (i : Position) :
    ((sourcePrefixEquiv counts labels depth t Position hinjective).symm word).val i =
      labelRecordOf labels depth (word.val i) := rfl

end Terminal

end MatrixMultiplication.Foundation.ConditionalPrefixWords

end

end OAI
