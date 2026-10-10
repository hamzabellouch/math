import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.CostDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.FieldDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.SimilarityDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.ShadowSimilarityDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.ApexPhysicalDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace CylinderCovering.Nilpotent
open RuledApproximation

def SweepCoverageStatement : Prop :=
  ∀ (k x y z : ℝ), 0 < k → k < 1 → InTetrahedron x y z →
    InLowerSweep k x y z ∨ InUpperSweep k x y z

def AngularFieldStatement : Prop :=
  (∀ σ k : ℝ, ContDiffOn ℝ ∞ (signedField σ k) {b : Plane | 0 < b 1}) ∧
  (∀ (σ k : ℝ) (b : Plane), b 1 ≠ 0 →
    HasFDerivAt (signedField σ k) (angularDerivative σ k b) b) ∧
  (∀ (σ k : ℝ) (b : Plane),
    (angularDerivative σ k b).comp (angularDerivative σ k b) = 0) ∧
  (∀ (σ k p t : ℝ), t ≠ 0 → ∀ z : Plane,
    angularDerivative σ k (vec2 (p * t) t) z =
      (σ * k / (2 * t) * (z 0 - p * z 1)) • vec2 p 1) ∧
  (∀ σ k : ℝ, σ * k ≠ 0 →
    ¬ ∃ F : Plane → Plane, ContinuousAt F 0 ∧
      ∀ b : Plane, 0 < b 1 → F b = signedField σ k b)

def IntegralCostStatement : Prop :=
  (∫ p in (-1 : ℝ)..1, a p) = 1 / 15 ∧
  (∫ p in (-1 : ℝ)..1, speedSq p) = 17 / 30 ∧
  (∀ k : ℝ, 0 ≤ k → k ≤ 1 →
    |I k - (1 / 4 - k ^ 2 / 480)| ≤ 4 * k ^ 3) ∧
  ((fun k : ℝ => I k - (1 / 4 - k ^ 2 / 480)) =O[𝓝[>] 0]
    (fun k : ℝ => k ^ 3)) ∧
  (∀ k : ℝ, 0 < k → k < 1 / 1920 → I k < 1 / 4)

def AuxiliaryApexStatement : Prop :=
  ∀ (h k ρ σ : ℝ), 0 ≤ k → 0 < ρ → ρ ≤ 1 → |σ| ≤ 1 →
    IsCompact (NilpotentApexNet.tile k ρ) ∧
    Convex ℝ (NilpotentApexNet.tile k ρ) ∧
    MeasurableSet (NilpotentApexNet.tile k ρ) ∧
    0 < (volume (NilpotentApexNet.tile k ρ)).toReal ∧
    (volume (NilpotentApexNet.tile k ρ)).toReal = (2 * (1 + k / 2) * ρ) ^ 2 ∧
    (NilpotentApexNet.meshCount ρ + 1 : ℕ) ≤ (4 / ρ : ℝ) ∧
    NilpotentApexNet.apexSweep k ρ σ ⊆
      ⋃ j : Fin (NilpotentApexNet.meshCount ρ + 1), NilpotentApexNet.cylinder k ρ σ j ∧
    (∑ j : Fin (NilpotentApexNet.meshCount ρ + 1),
      NilpotentApexNet.weightedArea h k ρ σ j) ≤ 16 * (1 + k / 2) ^ 2 * ρ

def PhysicalSimilarityStatement : Prop :=
  (∀ x y z : ℝ, centerMap (vec3 x y (Real.sqrt 2 * z)) =
    vec3 (x / 2) (y / 2) ((1 / 2 - z) / Real.sqrt 2)) ∧
  (∀ x y : Space, dist (centerMap x) (centerMap y) = dist x y / 2) ∧
  centerMap '' tetrahedron = SlopeRational.referenceTetrahedron ∧
  (∀ S : Set Space,
    (Measure.euclideanHausdorffMeasure 2 (centerMap '' S)).toReal =
      (Measure.euclideanHausdorffMeasure 2 S).toReal / 4) ∧
  (∀ S : Set Space, volume.real (centerMap '' S) = volume.real S / 8) ∧
  ShadowSimilarityStatement

def FiniteCounterexampleStatement : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Cylinder,
    (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
    tetrahedron ⊆ familySet C ∧
    familyArea C < minimumShadowArea tetrahedron / 2

def FullConstructionStatement : Prop :=
  volume.real tetrahedron = 2 * Real.sqrt 2 / 3 ∧
  minimumShadowArea tetrahedron = Real.sqrt 2 ∧
  SweepCoverageStatement ∧ AngularFieldStatement ∧ IntegralCostStatement ∧
  AuxiliaryApexStatement ∧ NilpotentApexNet.PhysicalApexNetStatement ∧
  PhysicalSimilarityStatement ∧ FiniteCounterexampleStatement

end CylinderCovering.Nilpotent

end

end OAI
