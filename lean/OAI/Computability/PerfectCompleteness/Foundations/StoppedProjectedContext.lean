import OAI.Computability.PerfectCompleteness.Foundations.GeometricPrefixSplit
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedExperiment
import OAI.Computability.PerfectCompleteness.Sampling.StoppedSharedSampler

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedContext

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t m : Nat}

abbrev Sample (rows : Nat → Nat) :=
  StoppedSharedSampler.Context branch n t m i rows ×
    SourceProjectedTag.Tag (branch := branch) (n := i) (t := t)

abbrev SplitSample (rows : Nat → Nat) :=
  StoppedProjectedExperiment.Outer (branch := branch) (n := n) (j := j) (t := t) (m := m) ×
    StoppedProjectedExperiment.Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows

variable (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)

def splitEquiv : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows ≃
    SplitSample (branch := branch) (n := n) (i := i) (j := j) (t := t) (m := m) rows where
  toFun x :=
    let prefixes := GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le) hupper x.1.2.1
    ((x.1.1, prefixes.1), (prefixes.2, (x.2, x.1.2.2)))
  invFun x :=
    ((x.1.1, ((GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le) hupper).symm
      (x.1.2, x.2.1), x.2.2.2)), x.2.2.1)
  left_inv x := by
    rcases x with ⟨⟨q, pref, directions⟩, tag⟩
    exact congrArg (fun pref => ((q, pref, directions), tag))
      ((GeometricPrefixSplit.splitEquiv (Nat.succ_le_succ hij.le) hupper).symm_apply_apply pref)
  right_inv x := by
    rcases x with ⟨⟨q, upper⟩, lower, tag, directions⟩
    simp only [Equiv.apply_symm_apply]

@[simp] theorem questions_split
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (splitEquiv rows hupper hij x).1.1 = x.1.1 := rfl

@[simp] theorem tag_split
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (splitEquiv rows hupper hij x).2.2.1 = x.2 := rfl

@[simp] theorem directions_split
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (splitEquiv rows hupper hij x).2.2.2 = x.1.2.2 := rfl

theorem stoppedPath_split (hi : i + 1 ≤ n)
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    StoppedProjectedExperiment.stoppedPath rows hupper hij
        (splitEquiv rows hupper hij x).1 (splitEquiv rows hupper hij x).2 =
      GeometricCutSplit.prefixPath hi x.1.2.1 :=
  (GeometricPrefixSplit.prefixPath_split (Nat.succ_le_succ hij.le) hupper x.1.2.1).symm

theorem lower_split (hi : i + 1 ≤ n)
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    StoppedProjectedExperiment.lower rows hupper hij
        (splitEquiv rows hupper hij x).1 (splitEquiv rows hupper hij x).2 =
      WholeArrayInteriorExterior.upperNode (GeometricCutSplit.prefixPath hi x.1.2.1) :=
  congrArg (fun p : Path branch n (i + 1) => WholeArrayInteriorExterior.upperNode p)
    (stoppedPath_split rows hupper hij hi x)

theorem fullPath_split_spec (hi : i + 1 ≤ n)
    (x : Sample (branch := branch) (n := n) (i := i) (t := t) (m := m) rows) :
    (⟨Nodes.height (StoppedProjectedExperiment.lower rows hupper hij
        (splitEquiv rows hupper hij x).1 (splitEquiv rows hupper hij x).2),
      WholeArrayInteriorOwnInputLaw.fullPath
        (StoppedProjectedExperiment.upper hupper (splitEquiv rows hupper hij x).1)
        (StoppedProjectedExperiment.lower rows hupper hij
          (splitEquiv rows hupper hij x).1 (splitEquiv rows hupper hij x).2)
        (StoppedProjectedExperiment.cut rows hupper hij
          (splitEquiv rows hupper hij x).1 (splitEquiv rows hupper hij x).2)⟩ :
      Σ height, Path branch n height) =
      ⟨i + 1, GeometricCutSplit.prefixPath hi x.1.2.1⟩ :=
  (StoppedProjectedExperiment.fullPath_spec rows hupper hij
    (splitEquiv rows hupper hij x).1 (splitEquiv rows hupper hij x).2).trans
      (congrArg (fun p : Path branch n (i + 1) =>
        (⟨i + 1, p⟩ : Σ height, Path branch n height))
        (stoppedPath_split rows hupper hij hi x))

variable [NeZero m] (hi : i + 1 ≤ n)
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)

theorem expectation_split
    (f : SplitSample (branch := branch) (n := n) (i := i) (j := j) (t := t) (m := m) rows → ℝ) :
    ((StoppedSharedSampler.contextLaw (cut := i) hi hbranch hrows).product
        (SourceProjectedTag.law (t := t) flag)).expectation
          (fun x => f (splitEquiv rows hupper hij x)) =
      ((StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch).product
        (StoppedProjectedExperiment.innerLaw rows hij
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag)).expectation f := by
  simp only [StoppedSharedSampler.contextLaw, StoppedProjectedExperiment.outerLaw,
    StoppedProjectedExperiment.innerLaw, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro q
  calc
    _ = (GeometricCutSplit.prefixLaw hupper hbranch).expectation (fun upper =>
        (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le)
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))).expectation (fun lower =>
          (CanonicalDirections.law rows n hrows).expectation (fun directions =>
            (SourceProjectedTag.law (t := t) flag).expectation (fun tag =>
              f ((q, upper), (lower, (tag, directions))))))) :=
      GeometricPrefixSplit.expectation_split (Nat.succ_le_succ hij.le) hupper hbranch
        (fun upper lower => (CanonicalDirections.law rows n hrows).expectation (fun directions =>
          (SourceProjectedTag.law (t := t) flag).expectation (fun tag =>
            f ((q, upper), (lower, (tag, directions))))))
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro upper
      apply FiniteDistribution.expectation_congr
      intro lower
      exact FiniteDistribution.expectation_comm _ _ _

theorem split_law :
    ((StoppedSharedSampler.contextLaw (cut := i) hi hbranch hrows).product
        (SourceProjectedTag.law (t := t) flag)).pushforward (splitEquiv rows hupper hij) =
      (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch).product
        (StoppedProjectedExperiment.innerLaw rows hij
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, CandidateCoupling.probability_eq_expectation,
    CandidateCoupling.probability_eq_expectation]
  exact expectation_split rows hupper hij hi hbranch hrows flag
    (fun x => if event x then 1 else 0)

end
end PerfectCompleteness.StoppedProjectedContext

end

end OAI
