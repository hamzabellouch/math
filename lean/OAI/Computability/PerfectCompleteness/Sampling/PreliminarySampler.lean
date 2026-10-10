import OAI.Computability.PerfectCompleteness.Foundations.GeometricPathLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionAlphabetLemmas
import OAI.Computability.PerfectCompleteness.Sampling.WholeArraySampler

namespace OAI

section

namespace PerfectCompleteness.PreliminarySampler

open RecursiveSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {v m n t : Nat} {branch rows repeats : Nat → Nat}

abbrev Questions (branch : Nat → Nat) (n t m : Nat) :=
  Slots branch n → Fin t → Fin m

def endpoints (E : Questions branch n t m) :
    Slots branch n → Fin t → SourceKeys.Endpoint v m :=
  fun leaf coordinate => .clause (E leaf coordinate)

abbrev Base (branch : Nat → Nat) (n t m : Nat) :=
  Questions branch n t m × Slots branch n

abbrev ArrayTape (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (b : Base branch n t m) :=
  WholeArraySampler.Tape rows repeats (GeometricPath.leafPath b.2)
    (sourceSlots clauses (endpoints b.1))

abbrev Choice (rows : Nat → Nat) (leaf : Slots branch n) :=
  (level : Fin n) × BucketSampler.Direction
    (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))

abbrev Raw (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :=
  (b : Base branch n t m) × (ArrayTape clauses rows repeats b × Choice rows b.2)

theorem directionNonempty (width : Nat) (positive : 0 < width) :
    Nonempty (BucketSampler.Direction width) := by
  refine ⟨⟨fun _ => 1, ?_⟩⟩
  intro hz
  have h := congrFun hz ⟨0, positive⟩
  change (1 : BucketSampler.F2) = 0 at h
  exact one_ne_zero h

def questionsLaw [NeZero m] : FiniteDistribution (Questions branch n t m) :=
  FiniteDistribution.uniform _

theorem questionsLaw_eq_product [NeZero m] :
    questionsLaw (branch := branch) (n := n) (t := t) (m := m) =
      FiniteProduct.law (fun _ : Slots branch n =>
        FiniteProduct.law (fun _ : Fin t => FiniteDistribution.uniform (Fin m))) := by
  simp only [UniformLinearImage.law_uniform]
  rfl

def baseLaw [NeZero m] (hbranch : ∀ k < n, 0 < branch k) :
    FiniteDistribution (Base branch n t m) :=
  questionsLaw.product (GeometricPath.law n hbranch)

def choiceLaw (leaf : Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) : FiniteDistribution (Choice rows leaf) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact CompletionSoundness.sigmaLaw (FiniteDistribution.uniform (Fin n)) fun level => by
    letI : Nonempty (BucketSampler.Direction
        (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
      directionNonempty _ (by rw [GeometricPath.nodeAtLevel_height]; exact hrows level.val)
    exact FiniteDistribution.uniform _

theorem choiceLaw_level (leaf : Slots branch n) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) (event : Fin n → Bool) :
    (choiceLaw leaf hn hrows).probability (fun c => event c.1) =
      (by
        letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        exact (FiniteDistribution.uniform (Fin n)).probability event) := by
  exact CompletionSoundness.sigmaLaw_probability_first _ _ event

def conditionalLaw (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hrows : ∀ k, 0 < rows (k + 1)) (b : Base branch n t m) :
    FiniteDistribution (ArrayTape clauses rows repeats b × Choice rows b.2) :=
  (WholeArraySampler.tapeLaw rows repeats (GeometricPath.leafPath b.2)
    (sourceSlots clauses (endpoints b.1))).product (choiceLaw b.2 hn hrows)

def law [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    FiniteDistribution (Raw clauses branch n t rows repeats) :=
  CompletionSoundness.sigmaLaw (baseLaw hbranch)
    (conditionalLaw clauses rows repeats hn hrows)

theorem law_base [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (event : Base branch n t m → Bool) :
    (law clauses rows repeats hn hbranch hrows).probability (fun e => event e.1) =
      (baseLaw hbranch).probability event :=
  CompletionSoundness.sigmaLaw_probability_first _ _ event

theorem law_probability [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (event : Raw clauses branch n t rows repeats → Bool) :
    (law clauses rows repeats hn hbranch hrows).probability event =
      (baseLaw hbranch).expectation (fun b =>
        (conditionalLaw clauses rows repeats hn hrows b).probability
          (fun tapeAndChoice => event ⟨b, tapeAndChoice⟩)) :=
  CompletionSoundness.sigmaLaw_probability _ _ event

def family (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) :
    HierarchicalGame.Family clauses branch n t rows (Raw clauses branch n t rows repeats) where
  endpoints e := endpoints e.1.1
  arrays e := WholeArraySampler.evaluate rows repeats (GeometricPath.leafPath e.1.2)
    (sourceSlots clauses (endpoints e.1.1)) e.2.1
  selected e := GeometricPath.nodeAtLevel e.1.2 e.2.2.1
  direction e := e.2.2.2.val
  nonzero e := e.2.2.2.property

theorem family_selected_height (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (e : Raw clauses branch n t rows repeats) :
    Nodes.height ((family clauses branch n t rows repeats).selected e) = e.2.2.1.val + 1 :=
  GeometricPath.nodeAtLevel_height _ _

def game [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :=
  HierarchicalGame.game (family clauses branch n t rows repeats)
    (law clauses rows repeats hn hbranch hrows)

theorem edge_at_most_two (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat)
    (e : Raw clauses branch n t rows repeats)
    (Q : HierarchicalGame.RightLabel (family clauses branch n t rows repeats)
      (HierarchicalGame.rightAt (family clauses branch n t rows repeats) e)) :
    Nat.card {P : HierarchicalGame.LeftLabel (family clauses branch n t rows repeats)
      (HierarchicalGame.leftAt (family clauses branch n t rows repeats) e) //
      HierarchicalGame.edge (family clauses branch n t rows repeats) e P = Q} ≤ 2 :=
  HierarchicalGame.edge_at_most_two _ e Q

theorem completeness [NeZero m] (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (game clauses branch n t rows repeats hn hbranch hrows).success
      (HierarchicalGame.satisfyingStrategy (family clauses branch n t rows repeats)
        assignment hsat) = 1 :=
  HierarchicalGame.success_satisfyingStrategy _ _ assignment hsat

end
end PerfectCompleteness.PreliminarySampler

end

end OAI
