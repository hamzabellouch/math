import Mathlib.Data.Fintype.Sigma
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import OAI.Computability.PerfectCompleteness.Algebra.MatrixTriangularFoldingLemmas
import OAI.Computability.PerfectCompleteness.Construction.DescendantSpacesLemmas
import OAI.Computability.PerfectCompleteness.Construction.RelativeDescendantProductsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GeometricPathLemmas
import OAI.Computability.PerfectCompleteness.Foundations.GlobalityLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ManyGoodRowsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.TupleIndexEmitterLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI


namespace PerfectCompleteness.HierarchicalFrozenTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev LowerNodes := {d : RelativeDescendantProducts.RelativeDescendant upper //
  Nodes.height d.val = lowerLevel}

def lowerIndex (d : LowerNodes upper lowerLevel) : {j : Nodes branch n // j ≠ upper} :=
  RelativeDescendantProducts.descendantIndex upper d.val

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

def knownSpace : Submodule F2 (NodeEmbedding.NumberedDomain slots → F2) :=
  HierarchicalKnownRows.knownSpace slots upper background (lowerIndex upper lowerLevel)

theorem knownSpace_le_rowSpace (hbranch : ∀ k < n, 0 < branch k) :
    knownSpace slots upper lowerLevel background ≤ NodeEmbedding.RowSpace slots upper :=
  RelativeDescendantProducts.relative_knownSpace_le_rowSpace slots hbranch upper background
    (fun d : LowerNodes upper lowerLevel => d.val)

def knownRows : Submodule F2 (NodeEmbedding.RowSpace slots upper) :=
  (knownSpace slots upper lowerLevel background).comap
    (NodeEmbedding.RowSpace slots upper).subtype

def sectionMap :
    (NodeEmbedding.RowSpace slots upper ⧸ knownRows slots upper lowerLevel background) →ₗ[F2]
      NodeEmbedding.RowSpace slots upper :=
  Classical.choose (MatrixRowQuotient.exists_section (knownRows slots upper lowerLevel background))

theorem sectionMap_spec :
    (knownRows slots upper lowerLevel background).mkQ.comp
      (sectionMap slots upper lowerLevel background) = LinearMap.id :=
  Classical.choose_spec (MatrixRowQuotient.exists_section (knownRows slots upper lowerLevel background))

theorem determined :
    RepresentativeMatrixTable.Determined (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
      (knownRows slots upper lowerLevel background) :=
  HierarchicalKnownRows.determined slots upper background (lowerIndex upper lowerLevel)

abbrev QuotientMatrix :=
  Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸ knownRows slots upper lowerLevel background)
    →ₗ[F2] Block rows upper

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def table (useful : QuotientMatrix slots upper lowerLevel background → Prop) :
    QuotientMatrix slots upper lowerLevel background →
      Option (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  RepresentativeMatrixTable.partialTable (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    σ (knownRows slots upper lowerLevel background) (sectionMap slots upper lowerLevel background) useful

theorem card_accepted_responses_le_two
    (a : Block rows upper) (ha : a ≠ 0)
    (X : HierarchicalMatrixTable.Matrix (rows := rows) slots upper) :
    Nat.card {y : Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper //
      ∃ h : NodeEmbedding.RowSpace slots upper,
        CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots slots)
          (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
          σ a (EvaluationMatrix.shift (NodeEmbedding.RowSpace slots upper) X a h) ∧
        RepresentativeMatrixTable.response (TreeCanonical.numberedSlots slots)
          (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
          σ (knownRows slots upper lowerLevel background) (sectionMap slots upper lowerLevel background)
          (EvaluationMatrix.shift (NodeEmbedding.RowSpace slots upper) X a h) = y} ≤ 2 :=
  RepresentativeMatrixTable.card_accepted_responses_le_two (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    σ (knownRows slots upper lowerLevel background) (sectionMap slots upper lowerLevel background)
    (sectionMap_spec slots upper lowerLevel background)
    (determined slots upper lowerLevel background) a ha X

end
end PerfectCompleteness.HierarchicalFrozenTables



namespace PerfectCompleteness.HierarchicalUsefulness

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

noncomputable section

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev Coarse :=
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper) ×
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background

instance coarseFintype : Fintype (Coarse (rows := rows) slots upper lowerLevel) := by
  letI : Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
    Fintype.ofFinite _
  letI (b : HierarchicalMatrixTable.Background (rows := rows) slots upper) :
      Fintype (HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel b) :=
    linearMapFintype
  exact inferInstance

def observe (arrays : Arrays slots rows) : Coarse (rows := rows) slots upper lowerLevel :=
  ⟨HierarchicalMatrixTable.backgroundOf slots upper arrays,
    MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays))
      (NodeEmbedding.matrix arrays upper)⟩

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)

def mark (z : Coarse (rows := rows) slots upper lowerLevel) : Bool :=
  UsefulMark.useful original (fun x => observe slots upper lowerLevel (arrays x)) lower κ z

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def table (background : HierarchicalMatrixTable.Background (rows := rows) slots upper) :
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background →
      Option (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  HierarchicalFrozenTables.table slots upper lowerLevel background σ
    (fun X => mark slots upper lowerLevel original arrays lower κ ⟨background, X⟩ = true)

theorem table_isSome (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) :
    (table slots upper lowerLevel original arrays lower κ σ background X).isSome =
      mark slots upper lowerLevel original arrays lower κ ⟨background, X⟩ := by
  unfold table HierarchicalFrozenTables.table RepresentativeMatrixTable.partialTable
  cases h : mark slots upper lowerLevel original arrays lower κ ⟨background, X⟩ <;>
    simp [h]

theorem table_defined_at_observation (x : Ω) :
    (table slots upper lowerLevel original arrays lower κ σ
      (observe slots upper lowerLevel (arrays x)).1
      (observe slots upper lowerLevel (arrays x)).2).isSome =
    UsefulMark.useful original (fun y => observe slots upper lowerLevel (arrays y))
      lower κ (observe slots upper lowerLevel (arrays x)) :=
  table_isSome slots upper lowerLevel original arrays lower κ σ _ _

theorem useful_upper_mass (upperEvent : Ω → Bool) (c : ℝ) (hc : 0 ≤ c)
    (hjoint : c ≤ original.probability (fun x => lower x && upperEvent x)) :
    c / 2 ≤ original.probability (fun x => upperEvent x &&
      (table slots upper lowerLevel original arrays lower (c / 2) σ
        (observe slots upper lowerLevel (arrays x)).1
        (observe slots upper lowerLevel (arrays x)).2).isSome) := by
  simpa only [table_defined_at_observation] using
    UsefulMark.useful_upper_ge_half original
      (fun x => observe slots upper lowerLevel (arrays x)) lower upperEvent c hc hjoint

end
end PerfectCompleteness.HierarchicalUsefulness



namespace PerfectCompleteness.HierarchicalInverseAdvice

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

noncomputable section

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

local instance backgroundFintype :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  Fintype.ofFinite _

abbrev Input (background : HierarchicalMatrixTable.Background (rows := rows) slots upper) :=
  Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
    HierarchicalFrozenTables.knownRows slots upper lowerLevel background)

local instance inputFintype
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper) :
    Fintype (Input slots upper lowerLevel background) := Fintype.ofFinite _

local instance valueFintype :
    Fintype (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

theorem mean_adviceMass_ge
    (backgroundLaw : FiniteDistribution
      (HierarchicalMatrixTable.Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper))
    (r : Nat) (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ backgroundLaw.expectation (fun background =>
      PartialTableInverse.nonzeroAgreement
        (HierarchicalUsefulness.table slots upper lowerLevel
          original arrays lower κ σ background))) :
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * rows (Nodes.height upper)) ≤
      backgroundLaw.expectation (fun background =>
        ManyGoodRows.adviceMass
          (HierarchicalUsefulness.table slots upper lowerLevel
            original arrays lower κ σ background) r ρ) := by
  let : Nonempty (Fin (rows (Nodes.height upper))) := ⟨⟨0, hrows⟩⟩
  have h := FamilyGoodRows.mean_adviceMass_ge backgroundLaw
    (fun background => HierarchicalUsefulness.table slots upper lowerLevel
      original arrays lower κ σ background)
    r ρ η hη hρ hρ1 hconstants hmean
  simpa only [Block, Module.finrank_fin_fun] using h

end
end PerfectCompleteness.HierarchicalInverseAdvice



namespace PerfectCompleteness.KnownSpaceDimension

open FactoredFunctionsDependent

variable {𝕜 Ω I : Type*} [Field 𝕜] {J : I → Type*}

abbrev GeneratorIndex (J : I → Type*) := Unit ⊕ (Σ i, J i × J i)

def generator (lower : Ω → (i : I) → J i → 𝕜) : GeneratorIndex J → Ω → 𝕜
  | .inl _ => 1
  | .inr ⟨i, t, u⟩ => fun x => lower x i t * lower x i u

theorem generator_range (lower : Ω → (i : I) → J i → 𝕜) :
    Set.range (generator lower) =
      {f | f = 1 ∨ ∃ (i : I) (t u : J i), f = fun x => lower x i t * lower x i u} := by
  ext f
  constructor
  · rintro ⟨index, rfl⟩
    rcases index with constantIndex | ⟨i, t, u⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, t, u, rfl⟩
  · rintro (rfl | ⟨i, t, u, rfl⟩)
    · exact ⟨.inl (), rfl⟩
    · exact ⟨.inr ⟨i, t, u⟩, rfl⟩

theorem quadraticSpan_eq_span_range (lower : Ω → (i : I) → J i → 𝕜) :
    dependentQuadraticSpan lower = Submodule.span 𝕜 (Set.range (generator lower)) := by
  rw [generator_range]
  rfl

section Finite

variable [Fintype I] [∀ i, Fintype (J i)]

theorem card_generatorIndex :
    Fintype.card (GeneratorIndex J) = 1 + ∑ i, (Fintype.card (J i)) ^ 2 := by
  simp only [GeneratorIndex, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_sigma, Fintype.card_prod, pow_two]

theorem finiteDimensional_quadraticSpan (lower : Ω → (i : I) → J i → 𝕜) :
    FiniteDimensional 𝕜 (dependentQuadraticSpan lower) := by
  rw [quadraticSpan_eq_span_range]
  exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range (generator lower))

theorem finrank_quadraticSpan_le (lower : Ω → (i : I) → J i → 𝕜) :
    Module.finrank 𝕜 (dependentQuadraticSpan lower) ≤
      1 + ∑ i, (Fintype.card (J i)) ^ 2 := by
  rw [quadraticSpan_eq_span_range, ← card_generatorIndex (J := J)]
  exact finrank_range_le_card (generator lower)

end Finite

open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat} {D : Type*} [Fintype D]

theorem finrank_knownSpace_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (descendant : D → {j : Nodes branch n // j ≠ upper}) :
    Module.finrank F2 (HierarchicalKnownRows.knownSpace slots upper background descendant) ≤
      1 + ∑ d, (rows (Nodes.height (descendant d).val)) ^ 2 := by
  let rowCount : D → Nat := fun d => rows (Nodes.height (descendant d).val)
  let lower : NodeEmbedding.NumberedDomain slots → (d : D) → Fin (rowCount d) → F2 :=
    HierarchicalKnownRows.lower slots upper background descendant
  change Module.finrank F2 (dependentQuadraticSpan lower) ≤ 1 + ∑ d : D, (rowCount d) ^ 2
  have hbound : Module.finrank F2 (dependentQuadraticSpan lower) ≤
      1 + ∑ d : D, (Fintype.card (Fin (rowCount d))) ^ 2 :=
    finrank_quadraticSpan_le (𝕜 := F2) (Ω := NodeEmbedding.NumberedDomain slots)
      (I := D) (J := fun d : D => Fin (rowCount d)) lower
  simpa only [Fintype.card_fin] using hbound

theorem finrank_knownSpace_comap_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n)
    (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (descendant : D → {j : Nodes branch n // j ≠ upper})
    (hgeometry : HierarchicalKnownRows.knownSpace slots upper background descendant ≤
      NodeEmbedding.RowSpace slots upper) :
    Module.finrank F2 ((HierarchicalKnownRows.knownSpace slots upper background descendant).comap
        (NodeEmbedding.RowSpace slots upper).subtype) ≤
      1 + ∑ d, (rows (Nodes.height (descendant d).val)) ^ 2 := by
  rw [(Submodule.comapSubtypeEquivOfLe hgeometry).finrank_eq]
  exact finrank_knownSpace_le slots upper background descendant

end PerfectCompleteness.KnownSpaceDimension


section

namespace PerfectCompleteness.DescendantSpaces.Path

open RecursiveSpaces

universe u

variable {branch : Nat → Nat} {n m k l : Nat}

def append : {n m k : Nat} → Path branch n m → Path branch m k → Path branch n k
  | _, _, _, .refl _, q => q
  | _, _, _, .step i p, q => .step i (append p q)

@[simp] theorem append_refl (q : Path branch n m) : (Path.refl n).append q = q := rfl

@[simp] theorem append_step (i : Fin (branch n)) (p : Path branch n m)
    (q : Path branch m k) : (Path.step i p).append q = Path.step i (p.append q) := rfl

@[simp] theorem append_refl_right (p : Path branch n m) : p.append (.refl m) = p := by
  induction p with
  | refl n => rfl
  | step i p ih => exact congrArg (Path.step i) ih

theorem append_assoc (p : Path branch n m) :
    ∀ (q : Path branch m k) (r : Path branch k l),
      (p.append q).append r = p.append (q.append r) := by
  induction p with
  | refl n => intro q r; rfl
  | step i p ih =>
      intro q r
      exact congrArg (Path.step i) (ih q r)

@[simp] theorem slotEmbedding_append (p : Path branch n m) :
    ∀ (q : Path branch m k) (s : Slots branch k),
      (p.append q).slotEmbedding s = p.slotEmbedding (q.slotEmbedding s) := by
  induction p with
  | refl n => intro q s; rfl
  | step i p ih =>
      intro q s
      exact congrArg (fun t => (i, t)) (ih q s)

theorem family_append (p : Path branch n m) (q : Path branch m k)
    (A : Slots branch n → Type u) :
    (p.append q).family A = q.family (p.family A) := by
  funext s
  exact congrArg A (slotEmbedding_append p q s)

theorem restriction_append_heq (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u) (x : Assignment A),
      HEq ((p.append q).restriction A x)
        (q.restriction (p.family A) (p.restriction A x)) := by
  induction p with
  | refl n => intro q A x; rfl
  | step i p ih =>
      intro q A x
      exact ih q (childFamily A i) (childRestriction A i x)

def appendAssignmentEquiv (p : Path branch n m) (q : Path branch m k)
    (A : Slots branch n → Type u) :
    Assignment ((p.append q).family A) ≃ Assignment (q.family (p.family A)) :=
  Equiv.cast (congrArg (fun B : Slots branch k → Type u => Assignment B)
    (family_append p q A))

theorem restriction_append (p : Path branch n m) (q : Path branch m k)
    (A : Slots branch n → Type u) (x : Assignment A) :
    appendAssignmentEquiv p q A ((p.append q).restriction A x) =
      q.restriction (p.family A) (p.restriction A x) := by
  apply eq_of_heq
  exact (cast_heq _ _).trans (restriction_append_heq p q A x)

theorem restriction_append_comp (p : Path branch n m) (q : Path branch m k)
    (A : Slots branch n → Type u) :
    appendAssignmentEquiv p q A ∘ (p.append q).restriction A =
      q.restriction (p.family A) ∘ p.restriction A := by
  funext x
  exact restriction_append p q A x

end PerfectCompleteness.DescendantSpaces.Path

namespace PerfectCompleteness.PathComposition

open RecursiveSpaces DescendantSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n m : Nat}

theorem append_leafPath (p : Path branch n m) :
    ∀ leaf : Slots branch m, p.append (GeometricPath.leafPath leaf) =
      GeometricPath.leafPath (p.slotEmbedding leaf) := by
  induction p with
  | refl n => intro leaf; rfl
  | step i p ih =>
      intro leaf
      exact congrArg (Path.step i) (ih leaf)

theorem exists_leafAtNode : ∀ {n : Nat} (leaf : Slots branch n) (level : Fin n),
    ∃ suffix : Slots branch (Nodes.height (GeometricPath.nodeAtLevel leaf level)),
      (Nodes.path (GeometricPath.nodeAtLevel leaf level)).slotEmbedding suffix = leaf := by
  intro n
  induction n with
  | zero => intro leaf level; exact Fin.elim0 level
  | succ n ih =>
      intro leaf level
      refine Fin.lastCases ?_ (fun lower => ?_) level
      · rw [GeometricPath.nodeAtLevel_last]
        exact ⟨leaf, rfl⟩
      · rw [GeometricPath.nodeAtLevel_castSucc]
        obtain ⟨suffix, hsuffix⟩ := ih leaf.2 lower
        exact ⟨suffix, Prod.ext rfl hsuffix⟩

noncomputable def leafAtNode (leaf : Slots branch n) (level : Fin n) :
    Slots branch (Nodes.height (GeometricPath.nodeAtLevel leaf level)) :=
  Classical.choose (exists_leafAtNode leaf level)

theorem leafAtNode_embedding (leaf : Slots branch n) (level : Fin n) :
    (Nodes.path (GeometricPath.nodeAtLevel leaf level)).slotEmbedding
        (leafAtNode leaf level) = leaf :=
  Classical.choose_spec (exists_leafAtNode leaf level)

theorem leafAtNode_unique (leaf : Slots branch n) (level : Fin n)
    (suffix : Slots branch (Nodes.height (GeometricPath.nodeAtLevel leaf level)))
    (hsuffix : (Nodes.path (GeometricPath.nodeAtLevel leaf level)).slotEmbedding suffix = leaf) :
    suffix = leafAtNode leaf level :=
  (Nodes.path (GeometricPath.nodeAtLevel leaf level)).slotEmbedding_injective
    (hsuffix.trans (leafAtNode_embedding leaf level).symm)

theorem leafPath_split (leaf : Slots branch n) (level : Fin n) :
    (Nodes.path (GeometricPath.nodeAtLevel leaf level)).append
        (GeometricPath.leafPath (leafAtNode leaf level)) = GeometricPath.leafPath leaf := by
  rw [append_leafPath, leafAtNode_embedding]

end PerfectCompleteness.PathComposition

end


namespace PerfectCompleteness.GeometricCutSplit

open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

def PrefixDepth (branch : Nat → Nat) (cutoff : Nat) : Nat → Type
  | 0 => Unit
  | depth + 1 => Fin (branch (cutoff + depth)) × PrefixDepth branch cutoff depth

instance prefixDepthFintype (branch : Nat → Nat) (cutoff depth : Nat) :
    Fintype (PrefixDepth branch cutoff depth) := by
  induction depth with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ depth ih =>
      letI : Fintype (PrefixDepth branch cutoff depth) := ih
      exact inferInstanceAs (Fintype
        (Fin (branch (cutoff + depth)) × PrefixDepth branch cutoff depth))

abbrev Prefix (branch : Nat → Nat) (root cutoff : Nat) :=
  PrefixDepth branch cutoff (root - cutoff)

def prefixPathDepth (cutoff : Nat) : (depth : Nat) →
    PrefixDepth branch cutoff depth → Path branch (cutoff + depth) cutoff
  | 0, _ => .refl cutoff
  | depth + 1, pref => .step pref.1 (prefixPathDepth cutoff depth pref.2)

def splitDepth (cutoff : Nat) : (depth : Nat) →
    Slots branch (cutoff + depth) ≃ PrefixDepth branch cutoff depth × Slots branch cutoff
  | 0 =>
      { toFun := fun suffix => ((), suffix)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, suffix⟩; rfl }
  | depth + 1 =>
      ((Equiv.refl (Fin (branch (cutoff + depth)))).prodCongr (splitDepth cutoff depth)).trans
        (Equiv.prodAssoc _ _ _).symm

theorem splitDepth_symm_eq_embedding (cutoff depth : Nat)
    (pref : PrefixDepth branch cutoff depth) (suffix : Slots branch cutoff) :
    (splitDepth cutoff depth).symm (pref, suffix) =
      (prefixPathDepth cutoff depth pref).slotEmbedding suffix := by
  revert pref
  induction depth with
  | zero => intro pref; rfl
  | succ depth ih =>
      intro pref
      change (pref.1, (splitDepth cutoff depth).symm (pref.2, suffix)) =
        (pref.1, (prefixPathDepth cutoff depth pref.2).slotEmbedding suffix)
      exact Prod.ext rfl (ih pref.2)

def castPath {a b cutoff : Nat} (h : a = b) (p : Path branch a cutoff) :
    Path branch b cutoff := h ▸ p

theorem castPath_embedding {a b cutoff : Nat} (h : a = b)
    (p : Path branch a cutoff) (suffix : Slots branch cutoff) :
    (castPath h p).slotEmbedding suffix =
      (Equiv.cast (congrArg (Slots branch) h)) (p.slotEmbedding suffix) := by
  cases h
  rfl

variable {root cutoff : Nat}

def prefixPath (hcut : cutoff ≤ root) (pref : Prefix branch root cutoff) :
    Path branch root cutoff :=
  castPath (Nat.add_sub_of_le hcut) (prefixPathDepth cutoff (root - cutoff) pref)

def joinEquiv (hcut : cutoff ≤ root) :
    Prefix branch root cutoff × Slots branch cutoff ≃ Slots branch root :=
  (splitDepth cutoff (root - cutoff)).symm.trans
    (Equiv.cast (congrArg (Slots branch) (Nat.add_sub_of_le hcut)))

def splitEquiv (hcut : cutoff ≤ root) :
    Slots branch root ≃ Prefix branch root cutoff × Slots branch cutoff :=
  (joinEquiv hcut).symm

theorem joinEquiv_apply (hcut : cutoff ≤ root)
    (pref : Prefix branch root cutoff) (suffix : Slots branch cutoff) :
    joinEquiv hcut (pref, suffix) = (prefixPath hcut pref).slotEmbedding suffix := by
  rw [prefixPath, castPath_embedding]
  change (Equiv.cast (congrArg (Slots branch) (Nat.add_sub_of_le hcut)))
      ((splitDepth cutoff (root - cutoff)).symm (pref, suffix)) = _
  exact congrArg (Equiv.cast (congrArg (Slots branch) (Nat.add_sub_of_le hcut)))
    (splitDepth_symm_eq_embedding cutoff (root - cutoff) pref suffix)

@[simp] theorem join_split (hcut : cutoff ≤ root) (leaf : Slots branch root) :
    joinEquiv hcut (splitEquiv hcut leaf) = leaf :=
  (joinEquiv hcut).apply_symm_apply leaf

@[simp] theorem split_embedding (hcut : cutoff ≤ root)
    (pref : Prefix branch root cutoff) (suffix : Slots branch cutoff) :
    splitEquiv hcut ((prefixPath hcut pref).slotEmbedding suffix) = (pref, suffix) := by
  rw [← joinEquiv_apply]
  exact (joinEquiv hcut).symm_apply_apply (pref, suffix)

theorem split_embedding_eq (hcut : cutoff ≤ root) (leaf : Slots branch root) :
    (prefixPath hcut (splitEquiv hcut leaf).1).slotEmbedding
        (splitEquiv hcut leaf).2 = leaf := by
  rw [← joinEquiv_apply]
  exact join_split hcut leaf

theorem leafPath_split (hcut : cutoff ≤ root) (leaf : Slots branch root) :
    (prefixPath hcut (splitEquiv hcut leaf).1).append
        (GeometricPath.leafPath (splitEquiv hcut leaf).2) = GeometricPath.leafPath leaf := by
  rw [PathComposition.append_leafPath, split_embedding_eq]

theorem prefix_nonempty (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k) : Nonempty (Prefix branch root cutoff) := by
  obtain ⟨leaf⟩ := GeometricPath.slots_nonempty root hbranch
  exact ⟨(splitEquiv hcut leaf).1⟩

noncomputable section

def prefixLaw (hcut : cutoff ≤ root) (hbranch : ∀ k < root, 0 < branch k) :
    FiniteDistribution (Prefix branch root cutoff) := by
  letI := prefix_nonempty hcut hbranch
  exact FiniteDistribution.uniform _

theorem law_split (hcut : cutoff ≤ root) (hbranch : ∀ k < root, 0 < branch k) :
    (GeometricPath.law root hbranch).pushforward (splitEquiv hcut) =
      (prefixLaw hcut hbranch).product
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (1 : ℝ) / (Fintype.card (Slots branch root) : ℝ) =
    ((1 : ℝ) / (Fintype.card (Prefix branch root cutoff) : ℝ)) *
      ((1 : ℝ) / (Fintype.card (Slots branch cutoff) : ℝ))
  rw [Fintype.card_congr (splitEquiv (branch := branch) hcut), Fintype.card_prod, Nat.cast_mul]
  simp only [one_div_mul_one_div]

theorem expectation_split (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k)
    (f : Prefix branch root cutoff → Slots branch cutoff → ℝ) :
    (GeometricPath.law root hbranch).expectation
        (fun leaf => f (splitEquiv hcut leaf).1 (splitEquiv hcut leaf).2) =
      (prefixLaw hcut hbranch).expectation (fun pref =>
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).expectation (f pref)) := by
  rw [← FiniteDistribution.expectation_pushforward
    (GeometricPath.law root hbranch) (splitEquiv hcut) (fun pair => f pair.1 pair.2),
    law_split, FiniteDistribution.expectation_product]

theorem probability_split (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k)
    (event : Prefix branch root cutoff × Slots branch cutoff → Bool) :
    (GeometricPath.law root hbranch).probability (fun leaf => event (splitEquiv hcut leaf)) =
      (prefixLaw hcut hbranch).expectation (fun pref =>
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).probability
            (fun suffix => event (pref, suffix))) := by
  rw [← FiniteDistribution.probability_pushforward
    (GeometricPath.law root hbranch) (splitEquiv hcut) event, law_split]
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end
end PerfectCompleteness.GeometricCutSplit



namespace PerfectCompleteness.GeometricCutMixture

open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root cutoff : Nat}
  {Γ : Type*} [Fintype Γ]

theorem mixture_split (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k)
    (experiment : Slots branch root → FiniteDistribution Γ) :
    (GeometricPath.law root hbranch).mixture experiment =
      (GeometricCutSplit.prefixLaw hcut hbranch).mixture (fun pref =>
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).mixture
            (fun suffix => experiment (GeometricCutSplit.joinEquiv hcut (pref, suffix)))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (GeometricPath.law root hbranch).expectation (fun leaf => (experiment leaf).weight x) =
    (GeometricCutSplit.prefixLaw hcut hbranch).expectation (fun pref =>
      (GeometricPath.law cutoff
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).expectation
          (fun suffix => (experiment (GeometricCutSplit.joinEquiv hcut (pref, suffix))).weight x))
  simpa only [Prod.mk.eta, GeometricCutSplit.join_split] using
    (GeometricCutSplit.expectation_split hcut hbranch
      (fun pref suffix => (experiment (GeometricCutSplit.joinEquiv hcut (pref, suffix))).weight x))

theorem path_mixture_split (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k)
    (experiment : Path branch root 0 → FiniteDistribution Γ) :
    (GeometricPath.law root hbranch).mixture
        (fun leaf => experiment (GeometricPath.leafPath leaf)) =
      (GeometricCutSplit.prefixLaw hcut hbranch).mixture (fun pref =>
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).mixture
            (fun suffix => experiment ((GeometricCutSplit.prefixPath hcut pref).append
              (GeometricPath.leafPath suffix)))) := by
  rw [mixture_split hcut hbranch]
  apply congrArg ((GeometricCutSplit.prefixLaw hcut hbranch).mixture)
  funext pref
  apply congrArg ((GeometricPath.law cutoff
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).mixture)
  funext suffix
  rw [GeometricCutSplit.joinEquiv_apply, PathComposition.append_leafPath]

end
end PerfectCompleteness.GeometricCutMixture

end OAI
