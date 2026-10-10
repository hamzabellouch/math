import OAI.Combinatorics.BalancedRyser.Local.LocalConditionUnusedSupport
import OAI.Combinatorics.BalancedRyser.Local.LocalPrecoverageTransport
import OAI.Combinatorics.BalancedRyser.Local.LocalSpecificationProbability

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {b κ : ℕ}

theorem admissibleBadCover_fixedUnused_bound
    (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) (bits : Bits b)
    (p : Point F) (N : MergedPairs F) (Ms : (α → F) → MergedPairs F)
    (u : Position b → α) (point : Position b → F → Point F)
    (I : Finset (Position b)) (hb : 1 ≤ b) (hB : 1 ≤ logBudget F)
    (hfixed : ∀ x d, d ∈ unusedDirections a → Ms x d = N d)
    (hpoints : ∀ x v, prescribedPoint P a bits (Ms x) v = point v (x (u v)))
    (hinj : ∀ v ∈ I, Function.Injective (point v))
    (hline : ∀ v ∈ I, ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p))
    (hextract : ∀ x, AdmissibleBadCover P a bits p (Ms x) →
      ∃ σ : Fin (3 - κ) → Position b × Code b κ,
        GoodSpecification u I σ ∧ ∀ k, Holds P a bits p (Ms x) (σ k).1 (σ k).2) :
    UnusedOffsetIncidence.probability
      (fun x : α → F => AdmissibleBadCover P a bits p (Ms x)) ≤
      (148 : ℝ) ^ 3 * (b : ℝ) ^ 9 *
        (2 * (logBudget F : ℝ) / Fintype.card F) ^ (3 - κ) := by
  by_cases hmult : ∀ y : Point F,
      (indexedThrough N (unusedDirections a) y).card ≤ logBudget F
  · apply (UnusedOffsetIncidence.probability_mono (fun x hx => ?_)).trans
      (specifications_probability_le a p N (logBudget F) hB hmult u point I hinj hline hb)
    obtain ⟨σ, hσ, hholds⟩ := hextract x hx
    refine ⟨σ, hσ, fun k => ?_⟩
    have hh := hholds k
    rw [holds_eq_pointHolds] at hh
    have heq : prescribedPoint P a bits (Ms x) = fun v => point v (x (u v)) :=
      funext (hpoints x)
    rw [heq] at hh
    exact (pointHolds_iff_of_unused_eq a p (Ms x) N
      (fun d hd => hfixed x d (by simpa [unusedDirections] using hd)) _ _ _).mp hh
  · have hempty : ∀ x : α → F, ¬ AdmissibleBadCover P a bits p (Ms x) := by
      intro x hx
      apply hmult
      intro y
      exact PrescribedGeometry.fixedUnused_multiplicity_le hx.1 (hfixed x) y
    simp only [UnusedOffsetIncidence.probability, hempty, Finset.filter_false,
      Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

end
end Balanced.Local.ConditionSpec

end OAI
