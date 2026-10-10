import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic

namespace OAI

universe uX uY

/-!
# A bounded greedy family of pivots

At each step, choose a set whose mass outside the current union exceeds the
threshold if such a set exists. Otherwise choose a fixed padding center.
Padding still enlarges the union, so it cannot increase any residual mass.
If the residual bound failed after `s` steps, all preceding steps would have
made a strict gain greater than the threshold, contradicting total mass at
most one and `1 ≤ s * θ`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

namespace GreedyPivots

variable {X : Type uX} {Y : Type uY}

/-- The mass of a finite set of columns. -/
def mass (μ : Y → ℝ) (U : Finset Y) : ℝ := ∑ y ∈ U, μ y

theorem mass_mono (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    {U V : Finset Y} (hUV : U ⊆ V) : mass μ U ≤ mass μ V :=
  Finset.sum_le_sum_of_subset_of_nonneg hUV (fun y _ _ => hμ y)

variable [Nonempty X] [DecidableEq Y]

/-- An active greedy pivot, or a fixed center when every residual is small. -/
def choosePivot (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (U : Finset Y) : X := by
  classical
  exact if h : ∃ x, θ < mass μ (I x \ U) then h.choose else Classical.choice inferInstance

theorem choosePivot_spec (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (U : Finset Y)
    (h : ∃ x, θ < mass μ (I x \ U)) :
    θ < mass μ (I (choosePivot μ I θ U) \ U) := by
  classical
  simpa only [choosePivot, dite_eq_left h] using h.choose_spec

/-- The union after exactly `n` selections, including any padding selections. -/
def covered (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) : ℕ → Finset Y
  | 0 => ∅
  | n + 1 => covered μ I θ n ∪ I (choosePivot μ I θ (covered μ I θ n))

@[simp] theorem covered_zero (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) :
    covered μ I θ 0 = ∅ := rfl

theorem covered_succ (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) :
    covered μ I θ (n + 1) =
      covered μ I θ n ∪ I (choosePivot μ I θ (covered μ I θ n)) := rfl

theorem covered_subset_succ (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) :
    covered μ I θ n ⊆ covered μ I θ (n + 1) := Finset.subset_union_left

theorem covered_mono (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) :
    Monotone (covered μ I θ) :=
  monotone_nat_of_le_succ (covered_subset_succ μ I θ)

omit [Nonempty X] in
theorem bad_of_subset (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) {U V : Finset Y} (hUV : U ⊆ V)
    (hV : ∃ x, θ < mass μ (I x \ V)) : ∃ x, θ < mass μ (I x \ U) := by
  obtain ⟨x, hx⟩ := hV
  refine ⟨x, hx.trans_le (mass_mono μ hμ ?_)⟩
  intro y hy
  obtain ⟨hyI, hyV⟩ := Finset.mem_sdiff.mp hy
  exact Finset.mem_sdiff.mpr ⟨hyI, fun hyU => hyV (hUV hyU)⟩

theorem mass_union (μ : Y → ℝ) (U V : Finset Y) :
    mass μ (U ∪ V) = mass μ U + mass μ (V \ U) := by
  calc
    mass μ (U ∪ V) = mass μ (U ∪ (V \ U)) :=
      congrArg (mass μ) Finset.union_sdiff_self_eq_union.symm
    _ = mass μ U + mass μ (V \ U) := Finset.sum_union Finset.disjoint_sdiff

theorem mass_covered_succ (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) :
    mass μ (covered μ I θ (n + 1)) = mass μ (covered μ I θ n) +
      mass μ (I (choosePivot μ I θ (covered μ I θ n)) \ covered μ I θ n) :=
  mass_union μ _ _

/-- A residual violation at a positive stage forces strict total mass growth
at every earlier stage, including the last one. -/
theorem mass_lt_of_bad (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (n : ℕ) :
    (∃ x, θ < mass μ (I x \ covered μ I θ n)) →
      n = 0 ∨ (n : ℝ) * θ < mass μ (covered μ I θ n) := by
  induction n with
  | zero =>
      intro _
      exact Or.inl rfl
  | succ n ih =>
      intro hbad
      have hprev := bad_of_subset μ I θ hμ (covered_subset_succ μ I θ n) hbad
      have hlower : (n : ℝ) * θ ≤ mass μ (covered μ I θ n) := by
        rcases ih hprev with hzero | hlt
        · subst n
          simp [mass]
        · exact hlt.le
      have hgain := choosePivot_spec μ I θ (covered μ I θ n) hprev
      right
      calc
        ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ := by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        _ < mass μ (covered μ I θ n) +
            mass μ (I (choosePivot μ I θ (covered μ I θ n)) \ covered μ I θ n) :=
          add_lt_add_of_le_of_lt hlower hgain
        _ = mass μ (covered μ I θ (n + 1)) := (mass_covered_succ μ I θ n).symm

theorem residual_le [Fintype Y] (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1) (s : ℕ)
    (hs : 1 ≤ (s : ℝ) * θ) (x : X) :
    mass μ (I x \ covered μ I θ s) ≤ θ := by
  have hs0 : s ≠ 0 := by
    intro hz
    subst s
    simp only [Nat.cast_zero, zero_mul] at hs
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hs
  apply le_of_not_gt
  intro hbad
  have hlower := mass_lt_of_bad μ I θ hμ s ⟨x, hbad⟩
  have hstrict := hlower.resolve_left hs0
  have hupper : mass μ (covered μ I θ s) ≤ 1 :=
    (mass_mono μ hμ (Finset.subset_univ _)).trans hmass
  exact (not_lt_of_ge hs) (hstrict.trans_le hupper)

/-- The recursive union consists exactly of the sets of its selected slots. -/
theorem mem_covered_iff (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) (y : Y) :
    y ∈ covered μ I θ n ↔
      ∃ k < n, y ∈ I (choosePivot μ I θ (covered μ I θ k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [covered_succ, Finset.mem_union, ih]
      constructor
      · rintro (⟨k, hk, hy⟩ | hy)
        · exact ⟨k, Nat.lt_succ_of_lt hk, hy⟩
        · exact ⟨n, Nat.lt_succ_self n, hy⟩
      · rintro ⟨k, hk, hy⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact Or.inl ⟨k, hlt, hy⟩
        · exact Or.inr hy

end GreedyPivots

/-- A finite family has a bounded number of pivots whose uncovered mass is
uniformly small. The assignment is supported exactly on the union of their
sets, and assigns a column only to a set containing it. -/
theorem exists_greedy_pivots {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
    (μ : Y → ℝ) (I : X → Finset Y) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) (θ : ℝ) (_hθ : 0 < θ) (s : ℕ)
    (hs : 1 ≤ (s : ℝ) * θ) :
    ∃ centers : Fin s → X, ∃ assigned : Y → Option (Fin s),
      (∀ y k, assigned y = some k → y ∈ I (centers k)) ∧
      (∀ y, (∃ k, y ∈ I (centers k)) ↔ assigned y ≠ none) ∧
      (∀ x, ∑ y ∈ (I x).filter (fun y => assigned y = none), μ y ≤ θ) := by
  classical
  let centers : Fin s → X := fun k =>
    GreedyPivots.choosePivot μ I θ (GreedyPivots.covered μ I θ k.val)
  let assigned : Y → Option (Fin s) := fun y =>
    if h : ∃ k, y ∈ I (centers k) then some h.choose else none
  have hmem : ∀ y k, assigned y = some k → y ∈ I (centers k) := by
    intro y k hk
    by_cases hy : ∃ j, y ∈ I (centers j)
    · have heq : hy.choose = k := by
        apply Option.some.inj
        simpa only [assigned, dite_eq_left hy] using hk
      exact heq ▸ hy.choose_spec
    · simp only [assigned, dite_eq_right hy] at hk
      cases hk
  have hsupport : ∀ y, (∃ k, y ∈ I (centers k)) ↔ assigned y ≠ none := by
    intro y
    by_cases hy : ∃ k, y ∈ I (centers k) <;> simp [assigned, hy]
  have hcovered : ∀ y, y ∈ GreedyPivots.covered μ I θ s ↔
      ∃ k, y ∈ I (centers k) := by
    intro y
    rw [GreedyPivots.mem_covered_iff]
    constructor
    · rintro ⟨k, hk, hy⟩
      exact ⟨⟨k, hk⟩, hy⟩
    · rintro ⟨k, hy⟩
      exact ⟨k.val, k.isLt, hy⟩
  have hnone : ∀ y, assigned y = none ↔ y ∉ GreedyPivots.covered μ I θ s := by
    intro y
    constructor
    · intro hn hy
      exact ((hsupport y).mp ((hcovered y).mp hy)) hn
    · intro hy
      by_cases hn : assigned y = none
      · exact hn
      · exact (hy ((hcovered y).mpr ((hsupport y).mpr hn))).elim
  refine ⟨centers, assigned, hmem, hsupport, ?_⟩
  intro x
  have hfilter : (I x).filter (fun y => assigned y = none) =
      I x \ GreedyPivots.covered μ I θ s := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff, hnone]
  rw [hfilter]
  exact GreedyPivots.residual_le μ I θ hμ hmass s hs x

end MetricEntropyDuality

end

end OAI
