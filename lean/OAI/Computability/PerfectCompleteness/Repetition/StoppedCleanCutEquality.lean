import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedExperiment
import OAI.Computability.PerfectCompleteness.Repetition.StoppedCleanGeometry

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanCutEquality

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat}

theorem append_left_injective {N M K : Nat} (pref : Path branch N M) :
    Function.Injective (fun suff : Path branch M K => pref.append suff) := by
  induction pref with
  | refl _ => intro a b hab; exact hab
  | step child pref ih =>
      intro a b hab
      apply ih
      change Path.step child (pref.append a) = Path.step child (pref.append b) at hab
      injection hab

theorem cut_eq_of_path_eq {N : Nat} {upper lower : Nodes branch N}
    (left right : OwnInputReference.Cut upper lower) (hpath : left.path = right.path) :
    left = right := by
  cases left
  cases right
  cases hpath
  rfl

theorem cut_heq_of_fullPath_heq {N : Nat} {upper lower₁ lower₂ : Nodes branch N}
    (hlower : lower₁ = lower₂)
    (left : OwnInputReference.Cut upper lower₁) (right : OwnInputReference.Cut upper lower₂)
    (hpath : HEq (WholeArrayInteriorOwnInputLaw.fullPath upper lower₁ left)
      (WholeArrayInteriorOwnInputLaw.fullPath upper lower₂ right)) : HEq left right := by
  cases hlower
  apply heq_of_eq
  apply cut_eq_of_path_eq
  exact append_left_injective (Nodes.path upper) (eq_of_heq hpath)

theorem cutOfBelow_heq_selectedCut {N i j : Nat}
    (p : Path branch N (j + 1)) (q : Path branch (j + 1) (i + 1)) (hij : i < j) :
    HEq (StoppedOwnInputGeometry.cutOfBelow (StoppedProjectedExperiment.below_append hij p q))
      (StoppedCleanGeometry.cut p q hij) := by
  refine cut_heq_of_fullPath_heq (StoppedCleanGeometry.lowerNode_descendant p q hij).symm
    _ _ ?_
  have hphysical : HEq
      (WholeArrayInteriorOwnInputLaw.fullPath (WholeArrayInteriorExterior.upperNode p)
        (WholeArrayInteriorExterior.upperNode (p.append q))
        (StoppedOwnInputGeometry.cutOfBelow (StoppedProjectedExperiment.below_append hij p q)))
      (p.append q) := by
    rw [StoppedOwnInputGeometry.fullPath_cutOfBelow]
    exact WholeArrayInteriorExterior.upperNode_path_heq (p.append q)
  exact hphysical.trans ((Sigma.mk.inj (StoppedCleanGeometry.fullPath_spec p q hij)).2.symm)

variable {n i j t m : Nat} (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))
  (k : StoppedProjectedExperiment.Inner
    (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)

theorem stopped_lower_eq :
    StoppedProjectedExperiment.lower rows hupper hij o k =
      HierarchicalLeftDecoder.LowerNode (StoppedProjectedExperiment.upper hupper o) (i + 1)
        (StoppedCleanGeometry.descendant (StoppedProjectedExperiment.upperPath hupper o)
          (StoppedProjectedExperiment.lowerPath rows hij k) hij) :=
  (StoppedCleanGeometry.lowerNode_descendant (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedExperiment.lowerPath rows hij k) hij).symm

theorem stopped_cut_heq :
    HEq (StoppedProjectedExperiment.cut rows hupper hij o k)
      (StoppedCleanGeometry.cut (StoppedProjectedExperiment.upperPath hupper o)
        (StoppedProjectedExperiment.lowerPath rows hij k) hij) :=
  cutOfBelow_heq_selectedCut (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedExperiment.lowerPath rows hij k) hij

end PerfectCompleteness.StoppedCleanCutEquality

end

end OAI
