import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeasureGroup
import Mathlib.Data.Finset.Max

namespace OAI

/-!
# Finitely many observables separate a compact set from the stabilizer

The eventual shearing contradiction only needs a fixed finite family
of generic observables. Continuity and compactness produce that family
and a uniform positive separation, directly from the actual measure
stabilizer. No empirical-convergence or homogeneous-orbit premise is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def invarianceDefect {n : ℕ} (μ : Measure (X n))
    (f : CompactlySupportedContinuousMap (X n) ℝ) (g : G n) : ℝ :=
  (∫ x, f (rightAction x g) ∂μ) - ∫ x, f x ∂μ

lemma continuous_invarianceDefect {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (f : CompactlySupportedContinuousMap (X n) ℝ) :
    Continuous (invarianceDefect μ f) :=
  (continuous_integral_rightAction μ f).sub continuous_const

lemma exists_nonzero_invarianceDefect {n : ℕ} (μ : Measure (X n)) [IsFiniteMeasure μ]
    (g : G n) (hg : g ∉ invariantRightSubgroup μ) :
    ∃ f : CompactlySupportedContinuousMap (X n) ℝ, invarianceDefect μ f g ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  change g ∈ (invariantRightSubgroup μ : Set (G n))
  rw [invariantRightSubgroup_eq_tests]
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro f
  exact sub_eq_zero.mp (h f)

/-- A fixed finite family distinguishes every possible limiting shear
in a compact set disjoint from the actual stabilizer. -/
theorem exists_finite_compact_stabilizer_separators {n : ℕ}
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (K : Set (G n)) (hK : IsCompact K)
    (hout : ∀ g ∈ K, g ∉ invariantRightSubgroup μ) :
    ∃ (F : Finset (CompactlySupportedContinuousMap (X n) ℝ)) (ε : ℝ),
      0 < ε ∧ ∀ g ∈ K, ∃ f ∈ F, ε < |invarianceDefect μ f g| := by
  by_cases hne : K.Nonempty
  · choose f hf using fun g : K => exists_nonzero_invarianceDefect μ g.val (hout g.val g.property)
    let e : K → ℝ := fun g => |invarianceDefect μ (f g) g.val| / 2
    have he (g : K) : 0 < e g := half_pos (abs_pos.mpr (hf g))
    let U : K → Set (G n) := fun g => {a | e g < |invarianceDefect μ (f g) a|}
    have hopen (g : K) : IsOpen (U g) :=
      isOpen_lt continuous_const (continuous_invarianceDefect μ (f g)).abs
    have hself (g : K) : g.val ∈ U g := by
      change |invarianceDefect μ (f g) g.val| / 2 < |invarianceDefect μ (f g) g.val|
      linarith [abs_pos.mpr (hf g)]
    have hcover : K ⊆ ⋃ g : K, U g := by
      intro g hg
      exact mem_iUnion.mpr ⟨⟨g, hg⟩, hself ⟨g, hg⟩⟩
    obtain ⟨J, hJ⟩ := hK.elim_finite_subcover U hopen hcover
    have hJne : J.Nonempty := by
      obtain ⟨g, hg⟩ := hne
      obtain ⟨a, ha, _⟩ := mem_iUnion₂.mp (hJ hg)
      exact ⟨a, ha⟩
    obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image J e hJne
    refine ⟨J.image f, e a, he a, ?_⟩
    intro g hg
    obtain ⟨b, hb, hgb⟩ := mem_iUnion₂.mp (hJ hg)
    exact ⟨f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, (hmin b hb).trans_lt hgb⟩
  · refine ⟨∅, 1, zero_lt_one, ?_⟩
    intro g hg
    exact (hne ⟨g, hg⟩).elim

end DukePrimeDegree

end

end OAI
