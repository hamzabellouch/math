import OAI.Analysis.Nonexpansive.MinimalInvariant
import OAI.Analysis.Nonexpansive.ScalarNormalization
import OAI.Analysis.Nonexpansive.WeakMetric

namespace OAI

/-!
# Full reduction of an original-norm counterexample

Starting from the given map, this producer constructs the separable minimal
invariant set, scales its points and conjugates its map in the same ambient
space, and proves the weak compactness and metrizability conclusions.
In particular the compact ball is the entire unit ball of the closed
linear span of the differences; compactness of the minimal set alone
would not supply that conclusion.
-/

noncomputable section

open Set TopologicalSpace

namespace ReflexiveFixedPoints

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A genuine original-norm fixed-point-free map produces all normalized
minimal invariant data used by the anchor and switching constructions. -/
theorem exists_normalizedMinimalData_of_counterexample
    (hX : CanonicallyReflexive X) {C : Set X}
    (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hconvex : Convex ℝ C)
    (F : C → C) (hF : LipschitzWith 1 F) (hno : ∀ x : C, F x ≠ x) :
    Nonempty (NormalizedMinimalData (X := X)) := by
  classical
  obtain ⟨D, _hDC⟩ := exists_minimalInvariantData_of_counterexample
    hX hne hclosed hbounded hconvex F hF hno
  let E := D.scaled hX (Metric.diam D.K)⁻¹ (inv_pos.mpr D.diam_pos)
  let : Nonempty E.K := E.nonempty.to_subtype
  let : SeparableSpace E.K := E.separable.separableSpace
  obtain ⟨z, hz⟩ := exists_dense_seq E.K
  exact ⟨{
    toMinimalInvariantData := E
    diam_one := D.scaled_inv_diam hX
    z := z
    dense_z := hz
    weak_metrizable := weakCarrier_metrizable E.separable E.weak_compact
    weak_ball_compact := weaklyCompact_differenceBall hX E.K
  }⟩

end ReflexiveFixedPoints

end

end OAI
