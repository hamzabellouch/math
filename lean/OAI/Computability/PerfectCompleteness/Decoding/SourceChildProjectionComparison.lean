import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.SourcePhysicalAssemblyLaw

namespace OAI

section

namespace PerfectCompleteness.SourceChildProjectionComparison

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open SourceChildKernel
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

theorem block_card_le (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype.card (Block C rows slots) ≤
      ChildBlockCardinality.bound branch n t (Fintype.card C) rows := by
  let e : Block C rows slots ≃
      ChildBlockCardinality.Raw (Fintype.card C) rows slots :=
    (Equiv.arrowCongr (Fintype.equivFin C)
      (Equiv.refl (squareSpace (H slots)))).prodCongr (Equiv.refl (Arrays slots rows))
  calc
    _ = Fintype.card (ChildBlockCardinality.Raw (Fintype.card C) rows slots) :=
      Fintype.card_congr e
    _ ≤ _ := ChildBlockCardinality.fintype_card_le (Fintype.card C) rows slots

def error (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) (β : ℝ) : ℝ :=
  Real.sqrt ((1 + β ^ 2 *
    ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^ branch n - 1) / 2

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem conditional_observed_variation {Γ : Type*} [Fintype Γ]
    (hbranch : 0 < branch n)
    (sources : Sources (m := m) (t := t) designated)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (observe : ((i : Fin (branch n)) →
      Native (C := C) (t := t) rows clauses designated i (sources i)) → Γ) :
    ((FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw
        (C := C) (t := t) rows clauses designated
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i (sources i))).pushforward
          observe).totalVariation
      ((FiniteProduct.law (fun i => FiniteDistribution.uniform
        (Native (C := C) (t := t) rows clauses designated i (sources i)))).pushforward
          observe) ≤ error branch n t (Fintype.card C) rows β := by
  let : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  let projected := fun i : Fin (branch n) =>
    (FiniteDistribution.uniform
      (Projected (C := C) (t := t) rows clauses designated i (sources i))).pushforward
        (SourceChildNativeLaw.pullback rows clauses designated i (sources i) true)
  have hcard : ∀ i : Fin (branch n),
      (Fintype.card (Native (C := C) (t := t) rows clauses designated i (sources i)) : ℝ) ≤
        (ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) := by
    intro i
    exact_mod_cast block_card_le (C := C) rows (nativeSlots clauses designated i (sources i))
  have h := SparseReplacement.observed_uniform_variation projected β hβ hβ'
    (ChildBlockCardinality.bound branch n t (Fintype.card C) rows : ℝ) hcard observe
  have hlaw : SparseReplacement.law
      (fun i => FiniteDistribution.uniform
        (Native (C := C) (t := t) rows clauses designated i (sources i)))
      projected β hβ hβ' =
      FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw
        (C := C) (t := t) rows clauses designated
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i (sources i)) := by
    rfl
  rw [hlaw] at h
  simpa only [error, Fintype.card_fin] using h

theorem conditional_assembled_variation
    (hbranch : 0 < branch n)
    (sources : Sources (m := m) (t := t) designated)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((FiniteProduct.law (fun i => SourceChildNativeLaw.leftLaw
        (C := C) (t := t) rows clauses designated
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ') i (sources i))).pushforward
          (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows)).totalVariation
      (FiniteDistribution.uniform
        (CutChildGrouping.Assembled (C := C) (parentLeftSlots clauses designated sources) rows)) ≤
      error branch n t (Fintype.card C) rows β := by
  have h := conditional_observed_variation rows clauses designated hbranch sources β hβ hβ'
    (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows)
  have huniform : (FiniteProduct.law (fun i => FiniteDistribution.uniform
      (Native (C := C) (t := t) rows clauses designated i (sources i)))).pushforward
        (CutChildGrouping.assemble (C := C) (parentLeftSlots clauses designated sources) rows) =
      FiniteDistribution.uniform
        (CutChildGrouping.Assembled (C := C) (parentLeftSlots clauses designated sources) rows) :=
    CutChildGrouping.assemble_law (C := C) (parentLeftSlots clauses designated sources) rows
  rw [huniform] at h
  exact h

theorem original_observed_variation [NeZero m] {Γ : Type*} [Fintype Γ]
    (hbranch : 0 < branch n) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (observe : SourcePhysicalAssemblyLaw.Observation (C := C) (t := t)
      rows clauses designated → Γ) :
    ((SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
          (fun sample => observe (SourcePhysicalAssemblyLaw.observe rows clauses designated sample))).totalVariation
      ((SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
        (fun _ => SourceChildNativeLaw.falseFlag)).pushforward
          (fun sample => observe (SourcePhysicalAssemblyLaw.observe rows clauses designated sample))) ≤
      error branch n t (Fintype.card C) rows β := by
  rw [← FiniteDistribution.pushforward_comp
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ'))
    (SourcePhysicalAssemblyLaw.observe rows clauses designated) observe,
    ← FiniteDistribution.pushforward_comp
      (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
        (fun _ => SourceChildNativeLaw.falseFlag))
      (SourcePhysicalAssemblyLaw.observe rows clauses designated) observe,
    SourcePhysicalAssemblyLaw.original_assembleLeft_law rows clauses designated
      (fun _ => ProjectionPosterior.bernoulli β hβ hβ'),
    SourcePhysicalAssemblyLaw.original_assembleLeft_false_law rows clauses designated]
  refine ConditionalVariation.observed_sigma_le_const _ _ _ _ ?_ observe
  intro sources
  exact conditional_assembled_variation rows clauses designated hbranch sources β hβ hβ'

end
end PerfectCompleteness.SourceChildProjectionComparison

end

end OAI
