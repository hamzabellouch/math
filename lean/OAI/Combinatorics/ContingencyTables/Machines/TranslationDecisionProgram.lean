import OAI.Combinatorics.ContingencyTables.Dense.DenseCompletionProgram
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellCatalogProgram
import OAI.Combinatorics.ContingencyTables.Transport.SignedMarginTranslation
import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialSemantics

namespace OAI

/-! # Binary arithmetic for the completion translation test -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms CompletionTranslation
open scoped BigOperators

abbrev MarginPair := List ℕ×List ℕ
abbrev TranslationCell := (MarginPair×MarginPair)×(ℕ×ℕ)
abbrev TranslationData := (MarginPair×MarginPair)×MatrixCode

def starParts (z : MarginPair×(ℕ×ℕ)) : ℕ×ℕ :=
  completionParts ((z.1,[]),z.2)

def starPartsRealizer : Realizer starParts :=
  composition (pair (pair first (constant [])) second) completionPartsRealizer

theorem polynomial_starParts : PolynomialTime starPartsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_second)
    polynomial_completionParts

def translationParts (z : TranslationCell) : ℕ×ℕ :=
  let old := starParts (z.1.1,z.2)
  let new := starParts (z.1.2,z.2)
  (new.1+old.2,new.2+old.1)

def translationPartsRealizer : Realizer translationParts := by
  let old : Realizer (fun z : TranslationCell => starParts (z.1.1,z.2)) :=
    composition (f := fun z : TranslationCell => (z.1.1,z.2)) (g := starParts)
      (pair (composition first first) second) starPartsRealizer
  let new : Realizer (fun z : TranslationCell => starParts (z.1.2,z.2)) :=
    composition (f := fun z : TranslationCell => (z.1.2,z.2)) (g := starParts)
      (pair (composition first second) second) starPartsRealizer
  exact pair (composition (pair (composition new first) (composition old second)) add)
    (composition (pair (composition new second) (composition old first)) add)

theorem polynomial_translationParts : PolynomialTime translationPartsRealizer := by
  have ho : PolynomialTime (composition (pair (composition
      (first (A := MarginPair×MarginPair) (B := ℕ×ℕ)) first) second) starPartsRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_starParts
  have hn : PolynomialTime (composition (pair (composition
      (first (A := MarginPair×MarginPair) (B := ℕ×ℕ)) second) second) starPartsRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_starParts
  unfold translationPartsRealizer
  exact polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition hn polynomial_first)
      (polynomial_composition ho polynomial_second)) polynomial_add)
    (polynomial_composition (polynomial_pair (polynomial_composition hn polynomial_second)
      (polynomial_composition ho polynomial_first)) polynomial_add)

def translatedCell (z : TranslationData×(ℕ×ℕ)) : Bool :=
  let p := translationParts (z.1.1,z.2)
  decide (p.2 ≤ matrixEntry (z.1.2,z.2)+p.1)

def translatedCellRealizer : Realizer translatedCell := by
  let parts : Realizer (fun z : TranslationData×(ℕ×ℕ) => translationParts (z.1.1,z.2)) :=
    composition (pair (composition first first) second) translationPartsRealizer
  let entry : Realizer (fun z : TranslationData×(ℕ×ℕ) => matrixEntry (z.1.2,z.2)) :=
    composition (pair (composition first second) second) matrixEntryRealizer
  exact composition (pair (composition parts second)
    (composition (pair entry (composition parts first)) add)) leNat

theorem polynomial_translatedCell : PolynomialTime translatedCellRealizer := by
  have hp : PolynomialTime (composition (pair (composition
      (first (A := TranslationData) (B := ℕ×ℕ)) first) second) translationPartsRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_translationParts
  have he : PolynomialTime (composition (pair (composition
      (first (A := TranslationData) (B := ℕ×ℕ)) second) second) matrixEntryRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_matrixEntry
  unfold translatedCellRealizer
  exact polynomial_composition (polynomial_pair (polynomial_composition hp polynomial_second)
    (polynomial_composition (polynomial_pair he (polynomial_composition hp polynomial_first))
      polynomial_add)) polynomial_leNat

def translationValid (z : TranslationData) : Bool :=
  (cellPairs z.1.1).all (fun ij => translatedCell (z,ij))

def translationValidRealizer : Realizer translationValid :=
  (composition (composition (pair identity (composition (composition first first) cellPairsRealizer))
    (mapWith translatedCellRealizer)) all).congr
    (by intro z; simp only [Function.comp_apply,Function.comp_def,List.all_map,id_eq,translationValid])

theorem polynomial_translationValid : PolynomialTime translationValidRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_cellPairs)) (polynomial_mapWith polynomial_translatedCell)) polynomial_all)

lemma starParts_code {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    ((starParts ((marginCode R,marginCode P),(optionIndex i,optionIndex j))).1:ℤ)-
      (starParts ((marginCode R,marginCode P),(optionIndex i,optionIndex j))).2=
      CompletionTranslation.star (fun i => (R i:ℤ)) (fun j => (P j:ℤ)) i j := by
  cases i <;> cases j <;>
    simp [starParts,completionParts,optionIndex,marginCode,List.sum_ofFn,
      matrixTotal,rowTotal,columnTotal,matrixEntry,CompletionTranslation.star]

lemma translationParts_code {m n : ℕ}
    (R₀ R₁ : Option (Fin m) → ℕ) (P₀ P₁ : Option (Fin n) → ℕ)
    (i : Option (Fin m)) (j : Option (Fin n)) :
    let p := translationParts (((marginCode R₀,marginCode P₀),(marginCode R₁,marginCode P₁)),
      (optionIndex i,optionIndex j))
    (p.1:ℤ)-p.2=between R₀ R₁ P₀ P₁ i j := by
  have h₀ := starParts_code R₀ P₀ i j
  have h₁ := starParts_code R₁ P₁ i j
  dsimp only [translationParts]
  simp only [Nat.cast_add]
  rw [show between R₀ R₁ P₀ P₁ i j=
    CompletionTranslation.star (fun i => (R₁ i:ℤ)) (fun j => (P₁ j:ℤ)) i j-
    CompletionTranslation.star (fun i => (R₀ i:ℤ)) (fun j => (P₀ j:ℤ)) i j by
      cases i <;> cases j <;> simp only [between,CompletionTranslation.star,Finset.sum_sub_distrib] <;> omega]
  omega

lemma tableOutput_entry {m n : ℕ} (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (X : Table R P) (i : Option (Fin m)) (j : Option (Fin n)) :
    matrixEntry (tableOutput X,(optionIndex i,optionIndex j))=X.val i j := by
  have hi : optionIndex i=((finSuccEquiv m).symm i).val := by
    cases i <;> simp only [optionIndex,finSuccEquiv_symm_none,finSuccEquiv_symm_some,
      Fin.val_zero,Fin.val_succ]
  have hj : optionIndex j=((finSuccEquiv n).symm j).val := by
    cases j <;> simp only [optionIndex,finSuccEquiv_symm_none,finSuccEquiv_symm_some,
      Fin.val_zero,Fin.val_succ]
  rw [hi,hj]
  unfold tableOutput
  rw [matrixEntry_code]
  simp only [Equiv.apply_symm_apply]

/-- Each binary comparison is the literal translated nonnegativity
condition in the Markov-chain acceptance decision. -/
theorem translatedCell_code {m n : ℕ}
    (R₀ R₁ : Option (Fin m) → ℕ) (P₀ P₁ : Option (Fin n) → ℕ)
    (X : Table R₀ P₀) (i : Option (Fin m)) (j : Option (Fin n)) :
    translatedCell ((((marginCode R₀,marginCode P₀),(marginCode R₁,marginCode P₁)),
      tableOutput X),(optionIndex i,optionIndex j))=true ↔
      0 ≤ (X.val i j:ℤ)+between R₀ R₁ P₀ P₁ i j := by
  have hp := translationParts_code R₀ R₁ P₀ P₁ i j
  dsimp only at hp
  simp only [translatedCell,decide_eq_true_eq,tableOutput_entry]
  omega

end ContingencyTables.DensePrograms

end OAI
