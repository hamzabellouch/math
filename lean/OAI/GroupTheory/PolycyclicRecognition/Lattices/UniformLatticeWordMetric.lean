import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeFiniteGeneration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordMetricBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProperCocompactMetric
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace OAI

/-!
# Comparing a lattice word metric with its ambient metric

The inclusion of a uniform lattice, equipped with any finite word metric,
is continuous and proper. Applying the proved chain argument therefore
gives both quasi-isometry inequalities and coarse surjectivity.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G]

/-- A uniform lattice with any finite word metric is quasi-isometric to its
ambient group, provided that the ambient metric has linear chains. -/
theorem IsUniformLattice.wordMetric_quasiIsometry {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G)
    {ι : Type*} [Finite ι] (P : Group.Generators Λ ι) :
    ∃ A B A' B' E : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ A' ∧ 0 ≤ B' ∧ 0 ≤ E ∧
      (∀ x y : Λ, dist (x : G) (y : G) ≤ A * (P.wordLength (x⁻¹ * y) : ℝ) + B) ∧
      (∀ x y : Λ, (P.wordLength (x⁻¹ * y) : ℝ) ≤ A' * dist (x : G) (y : G) + B') ∧
      (∀ g : G, ∃ x : Λ, dist g (x : G) ≤ E) := by
  have hfinite : ∀ K : Set G, IsCompact K → (Subtype.val ⁻¹' K : Set Λ).Finite := by
    let := hΛ.1
    have hclosed : IsClosed (Λ : Set G) := Subgroup.isClosed_of_discreteTopology
    intro K hK
    exact (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  let m := P.normedGroup.toMetricSpace
  let : MetricSpace Λ := m
  let : PseudoMetricSpace Λ := m.toPseudoMetricSpace
  let : PseudoEMetricSpace Λ := m.toPseudoMetricSpace.toPseudoEMetricSpace
  let : UniformSpace Λ := m.toUniformSpace
  let : TopologicalSpace Λ := m.toUniformSpace.toTopologicalSpace
  let : Dist Λ := m.toPseudoMetricSpace.toDist
  let : EDist Λ := m.toPseudoMetricSpace.toPseudoEMetricSpace.toEDist
  let : ProperSpace Λ := proper_wordMetric P
  let : DiscreteTopology Λ := discrete_wordMetric P
  let : IsIsometricSMul Λ Λ := ⟨fun g => Isometry.of_dist_eq (fun x y => by
    change (P.wordLength ((g * x)⁻¹ * (g * y)) : ℝ) = (P.wordLength (x⁻¹ * y) : ℝ)
    simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left])⟩
  have hf : Continuous (Λ.subtype : Λ → G) := continuous_of_discreteTopology
  have hproper : IsProperMap (Λ.subtype : Λ → G) := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hf, fun {K} hK => ?_⟩
    exact (hfinite K hK).isCompact
  exact proper_cocompact_hom_quasiIsometry (wordMetric_linearChains P) C
    Λ.subtype hf hproper K hK hcover

/-- The finite generating family can itself be obtained from compactness
and the ambient chains. No finite generation assumption is needed. -/
theorem IsUniformLattice.exists_wordMetric_quasiIsometry {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) (C : LinearMetricChains G) :
    ∃ (n : ℕ) (P : Group.Generators Λ (Fin n)),
      ∃ A B A' B' E : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ A' ∧ 0 ≤ B' ∧ 0 ≤ E ∧
        (∀ x y : Λ, dist (x : G) (y : G) ≤ A * (P.wordLength (x⁻¹ * y) : ℝ) + B) ∧
        (∀ x y : Λ, (P.wordLength (x⁻¹ * y) : ℝ) ≤ A' * dist (x : G) (y : G) + B') ∧
        (∀ g : G, ∃ x : Λ, dist g (x : G) ≤ E) := by
  let := hΛ.finitelyGenerated C
  obtain ⟨n, ⟨P⟩⟩ := Group.fg_iff_nonempty_finite_generators.mp (inferInstance : Group.FG Λ)
  exact ⟨n, P, hΛ.wordMetric_quasiIsometry C P⟩

end PolycyclicRecognition

end

end OAI
