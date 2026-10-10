import OAI.Analysis.SphereIsometry.KuratowskiBasic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace OAI

/-!
# Finite diameter covers and total boundedness

The Kuratowski cover predicate is equivalent to arbitrarily fine finite metric
covers. Its zero value characterizes total boundedness on bounded sets. A
selected point from each member of a nested family has totally bounded range
when sufficiently late members admit arbitrarily fine diameter covers.
-/

noncomputable section

open Set

namespace Tingley

universe u

variable {E : Type u} [PseudoMetricSpace E]

/-- Total boundedness is equivalent to finite pairwise-diameter covers at every
positive scale. No completeness or nonemptiness hypothesis is needed. -/
theorem totallyBounded_iff_finiteDiameterCover {H : Set E} :
    TotallyBounded H ↔ ∀ ε : ℝ, 0 < ε → FiniteDiameterCover H ε := by
  classical
  constructor
  · intro hH ε hε
    obtain ⟨t, ht, hcover⟩ :=
      Metric.totallyBounded_iff.mp hH (ε / 2) (half_pos hε)
    let : Fintype t := ht.fintype
    refine FiniteDiameterCover.of_fintype
      (fun c : t => Metric.ball (c : E) (ε / 2)) ?_ ?_
    · intro x hx
      obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact Set.mem_iUnion.mpr ⟨⟨c, hct⟩, hxc⟩
    · intro c x hx y hy
      have hxy : dist x y < ε := calc
        dist x y ≤ dist x (c : E) + dist y (c : E) := dist_triangle_right _ _ _
        _ < ε / 2 + ε / 2 :=
          add_lt_add (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hy)
        _ = ε := add_halves ε
      exact hxy.le
  · intro hcover
    apply Metric.totallyBounded_of_finite_discretization
    intro ε hε
    obtain ⟨n, A, hA, hdiam⟩ := hcover (ε / 2) (half_pos hε)
    have hmem : ∀ x : H, ∃ i : Fin n, (x : E) ∈ A i :=
      fun x => Set.mem_iUnion.mp (hA x.property)
    let label : H → Fin n := fun x => Classical.choose (hmem x)
    have hlabel : ∀ x : H, (x : E) ∈ A (label x) :=
      fun x => Classical.choose_spec (hmem x)
    refine ⟨ULift.{u} (Fin n), inferInstance,
      (fun x => ⟨label x⟩), ?_⟩
    intro x y hxy
    have heq : label x = label y :=
      congrArg (fun z : ULift.{u} (Fin n) => z.down) hxy
    have hy : (y : E) ∈ A (label x) := by
      rw [heq]
      exact hlabel y
    exact (hdiam (label x) (x : E) (hlabel x) (y : E) hy).trans_lt
      (half_lt_self hε)

/-- On bounded sets, vanishing Kuratowski measure is exactly total boundedness.
The boundedness premise ensures that the real infimum defining `chi` has
genuine admissible cover radii. -/
theorem chi_eq_zero_iff_totallyBounded {H : Set E}
    (hH : Bornology.IsBounded H) : chi H = 0 ↔ TotallyBounded H := by
  constructor
  · intro hzero
    apply totallyBounded_iff_finiteDiameterCover.mpr
    intro ε hε
    have hχε : chi H < ε := by
      rw [hzero]
      exact hε
    obtain ⟨δ, _hδ, hδε, hc⟩ := exists_cover_of_chi_lt hH hχε
    exact hc.mono_radius hδε.le
  · intro htb
    have hle : chi H ≤ 0 := by
      by_contra h
      have hpos : 0 < chi H := lt_of_not_ge h
      have hhalf : 0 < chi H / 2 := half_pos hpos
      have hcover := totallyBounded_iff_finiteDiameterCover.mp htb (chi H / 2) hhalf
      have hbound := chi_le_of_cover hhalf.le hcover
      exact (not_le_of_gt (half_lt_self hpos)) hbound
    exact le_antisymm hle (chi_nonneg hH)

/-- Cover the entire selected range by finitely many prefix singletons and a
small cover of a sufficiently late member. The cutoff may depend on the scale;
no fixed member of the original family is assumed totally bounded. -/
theorem totallyBounded_range_of_nested_finiteDiameterCover
    (C : ℕ → Set E) (hanti : Antitone C)
    (x : ℕ → E) (hx : ∀ n, x n ∈ C n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, FiniteDiameterCover (C N) ε) :
    TotallyBounded (Set.range x) := by
  classical
  apply totallyBounded_iff_finiteDiameterCover.mpr
  intro ε hε
  obtain ⟨N, k, A, hcover, hdiam⟩ := hsmall ε hε
  let B : Sum (Fin N) (Fin k) → Set E :=
    Sum.elim (fun i => {x (i : ℕ)}) A
  refine FiniteDiameterCover.of_fintype B ?_ ?_
  · rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨n, hn⟩, rfl⟩
    · have hxn : x n ∈ C N := hanti (Nat.le_of_not_gt hn) (hx n)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hxn)
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · intro i
    cases i with
    | inl i =>
      change DiameterLE ({x (i : ℕ)} : Set E) ε
      intro y hy z hz
      rcases Set.mem_singleton_iff.mp hy with rfl
      rcases Set.mem_singleton_iff.mp hz with rfl
      simpa only [dist_self] using hε.le
    | inr i =>
      exact hdiam i

end Tingley

end

end OAI
