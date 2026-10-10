import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import OAI.Computability.PerfectCompleteness.Algebra.EvaluationMatrix
import OAI.Computability.PerfectCompleteness.Algebra.MatrixErasure
import OAI.Computability.PerfectCompleteness.Algebra.MatrixInverseConstantsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.UniqueGames.Foundations.FiniteTrialsLemmas

namespace OAI


namespace PerfectCompleteness.ManyGoodRows

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.PartialTableInverse PerfectCompleteness.MatrixErasure

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

abbrev RowMap (F : Type*) [AddCommGroup F] [Module F2 F] (r : Nat) :=
  F →ₗ[F2] (Fin r → F2)

def GoodRow (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) : Prop :=
  ∃ (W : Submodule F2 E) (T : E →ₗ[F2] F) (y : Y),
    Module.finrank F2 W ≤ r ∧ A.comp T = U ∧
      ρ ≤ (𝔼 X : MatrixSlice.Slice W (LinearMap.ker A) T, indicator f y X.val)

structure Witness (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) where
  columnSpace : Submodule F2 E
  base : E →ₗ[F2] F
  value : Y
  column_count : Module.finrank F2 columnSpace ≤ r
  row_value : A.comp base = U
  density : ρ ≤ (𝔼 X : MatrixSlice.Slice columnSpace (LinearMap.ker A) base,
    indicator f value X.val)

def selectWitness (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (A : RowMap F r) (U : E →ₗ[F2] (Fin r → F2)) (h : GoodRow f r ρ A U) :
    Witness f r ρ A U :=
  Classical.choice (by
    obtain ⟨W, T, y, hW, hU, hdensity⟩ := h
    exact ⟨⟨W, T, y, hW, hU, hdensity⟩⟩)

def IsGoodPoint (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (X : E →ₗ[F2] F) : Prop :=
  ∃ A : RowMap F r, GoodRow f r ρ A (A.comp X)

def goodMass (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) : ℝ :=
  uniformMass (IsGoodPoint f r ρ)

def adviceMass (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) : ℝ :=
  𝔼 A : RowMap F r, 𝔼 X : E →ₗ[F2] F,
    if GoodRow f r ρ A (A.comp X) then (1 : ℝ) else 0

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem GoodRow.mono {f g : (E →ₗ[F2] F) → Option Y} {r : Nat} {ρ : ℝ}
    {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (h : GoodRow f r ρ A U)
    (hfg : ∀ y X, indicator f y X ≤ indicator g y X) : GoodRow g r ρ A U := by
  obtain ⟨W, T, y, hW, hU, hdensity⟩ := h
  refine ⟨W, T, y, hW, hU, hdensity.trans ?_⟩
  exact Finset.expect_le_expect fun X _ => hfg y X.val

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem isGoodPoint_of_witness {f : (E →ₗ[F2] F) → Option Y} {r : Nat} {ρ : ℝ}
    {W : Submodule F2 E} {A : RowMap F r} {T : E →ₗ[F2] F}
    (hgood : GoodRow f r ρ A (A.comp T))
    (X : MatrixSlice.Slice W (LinearMap.ker A) T) : IsGoodPoint f r ρ X.val := by
  refine ⟨A, ?_⟩
  rw [RowAdvice.slice_row_eq W A T X]
  exact hgood

omit [FiniteDimensional F2 E] [Fintype Y] in
theorem dense_restriction_rowMap (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F)
    (horder : order W C' ≤ r)
    (hdensity : ρ < (𝔼 N, restrict (indicator f y) W C' T N)) :
    ∃ A : RowMap F r,
      Module.finrank F2 W ≤ r ∧
      ρ < (𝔼 X : MatrixSlice.Slice W (LinearMap.ker A) T, indicator f y X.val) := by
  let hcodim := (MatrixSlice.row_count_le_order W C').trans horder
  let A := RowAdvice.paddedRowMap r C' hcodim
  have hker : LinearMap.ker A = C' := RowAdvice.ker_paddedRowMap r C' hcodim
  refine ⟨A, (MatrixSlice.column_count_le_order W C').trans horder, ?_⟩
  rw [hker]
  rwa [MatrixSlice.expect_restrict_eq_slice] at hdensity

theorem goodMass_ge [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    η / 4 ≤ goodMass f r ρ := by
  by_contra hsmall
  have hsmall' : goodMass f r ρ < η / 4 := lt_of_not_ge hsmall
  let erased := erase f (IsGoodPoint f r ρ)
  have herasure := nonzeroAgreement_erase f (IsGoodPoint f r ρ)
  have hremaining : η / 2 ≤ nonzeroAgreement erased := by
    change nonzeroAgreement f - 2 * goodMass f r ρ ≤ nonzeroAgreement erased at herasure
    linarith
  obtain ⟨y, W, C', T, horder, hdense⟩ :=
    exists_dense_slice_nonzero r ρ (η / 2) hρ hρ1 hconstants erased hremaining
  obtain ⟨A, hW, hdense'⟩ := dense_restriction_rowMap erased r ρ y W C' T horder hdense
  have hgoodErased : GoodRow erased r ρ A (A.comp T) :=
    ⟨W, T, y, hW, rfl, hdense'.le⟩
  have hgood : GoodRow f r ρ A (A.comp T) :=
    GoodRow.mono hgoodErased (indicator_erase_le f (IsGoodPoint f r ρ))
  have hzero : (𝔼 X : MatrixSlice.Slice W (LinearMap.ker A) T,
      indicator erased y X.val) = 0 := by
    apply Finset.expect_eq_zero
    intro X _
    have hX : IsGoodPoint f r ρ X.val := isGoodPoint_of_witness hgood X
    simp [indicator, erased, erase_eq_none_of f (IsGoodPoint f r ρ) hX]
  rw [hzero] at hdense'
  exact (not_lt_of_ge hρ.le) hdense'

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem goodMass_le_card_mul_adviceMass
    (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    goodMass f r ρ ≤ (Fintype.card (RowMap F r) : ℝ) * adviceMass f r ρ := by
  unfold goodMass uniformMass adviceMass
  rw [Fintype.card_mul_expect, ← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro X _
  by_cases hX : IsGoodPoint f r ρ X
  · rw [ite_eq_left hX]
    obtain ⟨A, hA⟩ := hX
    calc
      (1 : ℝ) = (if GoodRow f r ρ A (A.comp X) then 1 else 0) := by rw [ite_eq_left hA]
      _ ≤ ∑ B : RowMap F r, if GoodRow f r ρ B (B.comp X) then (1 : ℝ) else 0 := by
        apply Finset.single_le_sum
          (f := fun B : RowMap F r =>
            if GoodRow f r ρ B (B.comp X) then (1 : ℝ) else 0)
          (s := Finset.univ) (a := A)
        · intro B _
          split_ifs <;> norm_num
        · exact Finset.mem_univ A
  · rw [ite_eq_right hX]
    apply Finset.sum_nonneg
    intro A _
    split_ifs <;> norm_num

theorem adviceMass_ge [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    (η / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤ adviceMass f r ρ := by
  have hmass := (goodMass_ge r ρ η hρ hρ1 hconstants f hagreement).trans
    (goodMass_le_card_mul_adviceMass f r ρ)
  have hcard : (Fintype.card (RowMap F r) : ℝ) =
      (2 : ℝ) ^ (r * Module.finrank F2 F) := by
    exact_mod_cast RowAdvice.card_rowMaps (C := F) r
  rw [hcard] at hmass
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  simpa only [mul_comm] using hmass

theorem exists_uniform_parameters {η : ℝ} (hη : 0 < η) :
    ∃ r : Nat, 1 ≤ r ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ (E F Y : Type*)
        [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
        [FiniteDimensional F2 E] [FiniteDimensional F2 F]
        [Fintype E] [Fintype F] [Fintype Y] [Nontrivial F]
        (f : (E →ₗ[F2] F) → Option Y),
        η ≤ nonzeroAgreement f →
          η / 4 ≤ goodMass f r ρ ∧
          (η / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤ adviceMass f r ρ := by
  obtain ⟨r, hr, ρ, hρ, hρ1, hconstants⟩ :=
    MatrixInverseConstants.exists_cutoff_density (show 0 < η / 2 by positivity)
  refine ⟨r, hr, ρ, hρ, hρ1, ?_⟩
  intro E F Y _ _ _ _ _ _ _ _ _ _ f hagreement
  exact ⟨goodMass_ge r ρ η hρ hρ1 hconstants f hagreement,
    adviceMass_ge r ρ η hρ hρ1 hconstants f hagreement⟩

end
end PerfectCompleteness.ManyGoodRows



namespace PerfectCompleteness.FamilyGoodRows

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.PartialTableInverse PerfectCompleteness.MatrixErasure
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P]

theorem expectation_le_threshold_add_probability (μ : FiniteDistribution P)
    (g : P → ℝ) (η : ℝ) (hη : 0 ≤ η) (hg : ∀ p, g p ≤ 1) :
    μ.expectation g ≤ η + μ.probability (fun p => decide (η ≤ g p)) := by
  have hpoint : ∀ p, g p ≤ η + (if η ≤ g p then (1 : ℝ) else 0) := by
    intro p
    by_cases hp : η ≤ g p
    · rw [ite_eq_left hp]
      linarith [hg p]
    · rw [ite_eq_right hp, add_zero]
      exact (lt_of_not_ge hp).le
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
    mul_le_mul_of_nonneg_left (hpoint p) (μ.nonnegative p))
  simpa only [FiniteDistribution.expectation, FiniteDistribution.probability,
    mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    ← Finset.sum_mul, μ.normalized, one_mul, decide_eq_true_eq] using hsum

theorem threshold_probability_ge (μ : FiniteDistribution P) (g : P → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hg : ∀ p, g p ≤ 1)
    (hmean : 2 * η ≤ μ.expectation g) :
    η ≤ μ.probability (fun p => decide (η ≤ g p)) := by
  have h := expectation_le_threshold_add_probability μ g η hη hg
  linarith

theorem probability_mul_le_expectation (μ : FiniteDistribution P)
    (S : P → Prop) (g : P → ℝ) (c : ℝ)
    (hnonneg : ∀ p, 0 ≤ g p) (hgood : ∀ p, S p → c ≤ g p) :
    μ.probability (fun p => decide (S p)) * c ≤ μ.expectation g := by
  calc
    _ = μ.expectation (fun p => if S p then c else 0) := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        decide_eq_true_eq, Finset.sum_mul, ite_mul, mul_ite, zero_mul, mul_zero]
    _ ≤ μ.expectation g := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (μ.nonnegative p)
      by_cases hp : S p
      · simpa only [ite_eq_left hp] using hgood p hp
      · simpa only [ite_eq_right hp] using hnonneg p

section TableBounds

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem nonzeroAgreement_le_one [Nontrivial F]
    (f : (E →ₗ[F2] F) → Option Y) : nonzeroAgreement f ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  let : Nonempty {a : F // a ≠ 0} := ⟨⟨a, ha⟩⟩
  unfold nonzeroAgreement stepAgreement
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  apply Finset.expect_le Finset.univ_nonempty
  intro X _
  apply Finset.expect_le Finset.univ_nonempty
  intro h _
  exact definedEquality_le_one f X (X + h.smulRight a.val)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem adviceMass_nonneg (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    0 ≤ adviceMass f r ρ := by
  unfold adviceMass
  apply Finset.expect_nonneg
  intro A _
  apply Finset.expect_nonneg
  intro X _
  split_ifs <;> norm_num

end TableBounds


variable {E Y : P → Type*} {F : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F] [Fintype F] [Nontrivial F]
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)] [∀ p, Fintype (Y p)]

theorem mean_adviceMass_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F) → Option (Y p))
    (r : Nat) (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      μ.expectation (fun p => adviceMass (f p) r ρ) := by
  let c : ℝ := (η / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F)
  have hc : 0 ≤ c := by
    exact div_nonneg (div_nonneg hη.le (by norm_num)) (by positivity)
  have hmass : η ≤ μ.probability (fun p => decide (η ≤ nonzeroAgreement (f p))) :=
    threshold_probability_ge μ (fun p => nonzeroAgreement (f p)) η hη.le
      (fun p => nonzeroAgreement_le_one (f p)) hmean
  have hweighted :
      μ.probability (fun p => decide (η ≤ nonzeroAgreement (f p))) * c ≤
        μ.expectation (fun p => adviceMass (f p) r ρ) := by
    apply probability_mul_le_expectation μ
      (fun p => η ≤ nonzeroAgreement (f p)) (fun p => adviceMass (f p) r ρ) c
    · intro p
      exact adviceMass_nonneg (f p) r ρ
    · intro p hp
      exact ManyGoodRows.adviceMass_ge r ρ η hρ hρ1 hconstants (f p) hp
  calc
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F) = η * c := by
      dsimp [c]
      ring
    _ ≤ μ.probability (fun p => decide (η ≤ nonzeroAgreement (f p))) * c :=
      mul_le_mul_of_nonneg_right hmass hc
    _ ≤ μ.expectation (fun p => adviceMass (f p) r ρ) := hweighted

end
end PerfectCompleteness.FamilyGoodRows



namespace PerfectCompleteness.ProductEvaluation

open MixedSupport CanonicalKeys

abbrev F2 := ZMod 2

variable {X C Z : Type*} {Row : C → Type*}

inductive Generator (C : Type*) (Row : C → Type*) where
  | one
  | product (descendant : C) (first second : Row descendant)

def displayedJoint (rows : (c : C) → Row c → X → F2) (other : X → Z) (x : X) :
    ((c : C) → Row c → F2) × Z :=
  ((fun c u => rows c u x), other x)

def generatorValue (values : (c : C) → Row c → F2) : Generator C Row → F2
  | .one => 1
  | .product c u v => values c u * values c v

def generator (H : Submodule F2 (X → F2)) (rows : (c : C) → Row c → X → F2)
    (hone : (1 : X → F2) ∈ H)
    (hproducts : ∀ c u v, rows c u * rows c v ∈ H) : Generator C Row → H
  | .one => ⟨1, hone⟩
  | .product c u v => ⟨rows c u * rows c v, hproducts c u v⟩

def productSpan (H : Submodule F2 (X → F2)) (rows : (c : C) → Row c → X → F2)
    (hone : (1 : X → F2) ∈ H)
    (hproducts : ∀ c u v, rows c u * rows c v ∈ H) : Submodule F2 H :=
  Submodule.span F2 (Set.range (generator H rows hone hproducts))

def spanGenerator (H : Submodule F2 (X → F2)) (rows : (c : C) → Row c → X → F2)
    (hone : (1 : X → F2) ∈ H)
    (hproducts : ∀ c u v, rows c u * rows c v ∈ H) (g : Generator C Row) :
    productSpan H rows hone hproducts :=
  ⟨generator H rows hone hproducts g, Submodule.subset_span ⟨g, rfl⟩⟩

theorem functional_ext (H : Submodule F2 (X → F2))
    (rows : (c : C) → Row c → X → F2) (hone : (1 : X → F2) ∈ H)
    (hproducts : ∀ c u v, rows c u * rows c v ∈ H)
    (b b' : Module.Dual F2 (productSpan H rows hone hproducts))
    (h : ∀ g, b (spanGenerator H rows hone hproducts g) =
      b' (spanGenerator H rows hone hproducts g)) : b = b' := by
  apply (Submodule.linearMap_eq_iff_of_eq_span b b'
    (show productSpan H rows hone hproducts =
      Submodule.span F2 (Set.range (generator H rows hone hproducts)) from rfl)).2
  rintro ⟨u, ⟨g, rfl⟩⟩
  exact h g


variable {n : Nat}
variable (slots : Fin n → Slot)
variable (H : Submodule F2 (Assignment slots → F2))
variable (rows : (c : C) → Row c → Assignment slots → F2)
variable (other : Assignment slots → Z)
variable (hone : (1 : Assignment slots → F2) ∈ H)
variable (hproducts : ∀ c u v, rows c u * rows c v ∈ H)

noncomputable def realizingPoint (P : Label slots (displayedJoint rows other)) :
    Assignment slots :=
  ReducedPartition.representative (reduction slots (displayedJoint rows other))
    (displayedJoint rows other) P

theorem realizingPoint_joint (P : Label slots (displayedJoint rows other)) :
    displayedJoint rows other (realizingPoint slots rows other P) =
      restore slots (displayedJoint rows other) P := rfl

noncomputable def restoredRows (P : Label slots (displayedJoint rows other)) :
    (c : C) → Row c → F2 :=
  (restore slots (displayedJoint rows other) P).1

@[simp] theorem restoredRows_apply (P : Label slots (displayedJoint rows other))
    (c : C) (u : Row c) :
    restoredRows slots rows other P c u = rows c u (realizingPoint slots rows other P) := rfl

noncomputable def labelExtension (P : Label slots (displayedJoint rows other)) :
    Module.Dual F2 H :=
  EvaluationMatrix.evaluation H (realizingPoint slots rows other P)

noncomputable def labelFunctional (P : Label slots (displayedJoint rows other)) :
    Module.Dual F2 (productSpan H rows hone hproducts) :=
  (labelExtension slots H rows other P).comp (productSpan H rows hone hproducts).subtype

theorem labelFunctional_generators (P : Label slots (displayedJoint rows other))
    (g : Generator C Row) :
    labelFunctional slots H rows other hone hproducts P (spanGenerator H rows hone hproducts g) =
      generatorValue (restoredRows slots rows other P) g := by
  cases g <;> rfl

theorem labelFunctional_unique (P : Label slots (displayedJoint rows other))
    (b : Module.Dual F2 (productSpan H rows hone hproducts))
    (h : ∀ g, b (spanGenerator H rows hone hproducts g) =
      generatorValue (restoredRows slots rows other P) g) :
    b = labelFunctional slots H rows other hone hproducts P := by
  apply functional_ext H rows hone hproducts
  intro g
  exact (h g).trans (labelFunctional_generators slots H rows other hone hproducts P g).symm

theorem exists_unique_labelFunctional (P : Label slots (displayedJoint rows other)) :
    ∃! b : Module.Dual F2 (productSpan H rows hone hproducts),
      ∀ g, b (spanGenerator H rows hone hproducts g) =
        generatorValue (restoredRows slots rows other P) g := by
  refine ⟨labelFunctional slots H rows other hone hproducts P,
    labelFunctional_generators slots H rows other hone hproducts P, ?_⟩
  intro b hb
  exact labelFunctional_unique slots H rows other hone hproducts P b hb

theorem labelFunctional_eq_of_restoredRows_eq
    (P Q : Label slots (displayedJoint rows other))
    (h : restoredRows slots rows other P = restoredRows slots rows other Q) :
    labelFunctional slots H rows other hone hproducts P =
      labelFunctional slots H rows other hone hproducts Q := by
  apply functional_ext H rows hone hproducts
  intro g
  rw [labelFunctional_generators, labelFunctional_generators, h]

theorem labelExtension_restrict (P : Label slots (displayedJoint rows other)) :
    (labelExtension slots H rows other P).comp (productSpan H rows hone hproducts).subtype =
      labelFunctional slots H rows other hone hproducts P := rfl

theorem exists_labelExtension (P : Label slots (displayedJoint rows other)) :
    ∃ z : Module.Dual F2 H,
      z.comp (productSpan H rows hone hproducts).subtype =
        labelFunctional slots H rows other hone hproducts P :=
  ⟨labelExtension slots H rows other P, rfl⟩

theorem extension_generators (P : Label slots (displayedJoint rows other))
    (z : Module.Dual F2 H)
    (hz : z.comp (productSpan H rows hone hproducts).subtype =
      labelFunctional slots H rows other hone hproducts P) (g : Generator C Row) :
    z (generator H rows hone hproducts g) =
      generatorValue (restoredRows slots rows other P) g := by
  have h := congrArg (fun b : Module.Dual F2 (productSpan H rows hone hproducts) =>
    b (spanGenerator H rows hone hproducts g)) hz
  exact h.trans (labelFunctional_generators slots H rows other hone hproducts P g)

theorem extension_one (P : Label slots (displayedJoint rows other))
    (z : Module.Dual F2 H)
    (hz : z.comp (productSpan H rows hone hproducts).subtype =
      labelFunctional slots H rows other hone hproducts P) : z ⟨1, hone⟩ = 1 :=
  extension_generators slots H rows other hone hproducts P z hz .one

theorem extension_products (P : Label slots (displayedJoint rows other))
    (z : Module.Dual F2 H)
    (hz : z.comp (productSpan H rows hone hproducts).subtype =
      labelFunctional slots H rows other hone hproducts P) (c : C) (u v : Row c) :
    z ⟨rows c u * rows c v, hproducts c u v⟩ =
      restoredRows slots rows other P c u * restoredRows slots rows other P c v :=
  extension_generators slots H rows other hone hproducts P z hz (.product c u v)

theorem extension_productMatrix (P : Label slots (displayedJoint rows other))
    (z : Module.Dual F2 H)
    (hz : z.comp (productSpan H rows hone hproducts).subtype =
      labelFunctional slots H rows other hone hproducts P) (c : C) :
    (fun u v : Row c => z ⟨rows c u * rows c v, hproducts c u v⟩) =
      (fun u v : Row c =>
        restoredRows slots rows other P c u * restoredRows slots rows other P c v) := by
  funext u v
  exact extension_products slots H rows other hone hproducts P z hz c u v

end PerfectCompleteness.ProductEvaluation

end OAI
