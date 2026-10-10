import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.GeometricCompact
import OAI.Geometry.TamingCompatibility.HeatFlow.VariationalResolvent

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma graphEnergy_coercive : IsCoercive
    (Variational.energy (energyInclusion A J α hs ht) (weakDelta A J α hs ht)) := by
  refine ⟨1,zero_lt_one,fun u => ?_⟩
  rw [Variational.energy_apply,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have h := WithLp.prod_norm_sq_eq_of_L2 u.val
  change 1 * ‖u.val‖ * ‖u.val‖ ≤ ‖u.val.fst‖^2 + ‖u.val.snd‖^2
  nlinarith

def harmonicAnti : Submodule ℝ (L2 A J α hs ht true) :=
  Fredholm.nullspace (Variational.resolvent (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht))

lemma harmonicAnti_closed : _root_.IsClosed (harmonicAnti A J α hs ht : Set (L2 A J α hs ht true)) :=
  (1 - Variational.resolvent (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht)).isClosed_ker

instance harmonicAnti_complete : CompleteSpace (harmonicAnti A J α hs ht) :=
  (harmonicAnti_closed A J α hs ht).completeSpace_coe

lemma mem_harmonicAnti (f : L2 A J α hs ht true) :
    f ∈ harmonicAnti A J α hs ht ↔ ∃ u : antiEnergy A J α hs ht,
      energyInclusion A J α hs ht u = f ∧ weakDelta A J α hs ht u = 0 :=
  Variational.mem_nullspace_iff (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht) f

theorem geometric_weak_inverse
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source) :
    FiniteDimensional ℝ (harmonicAnti A J α hs ht) ∧
      ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
        (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
          ⟪f - (harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
        (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
        (∀ f ∈ harmonicAnti A J α hs ht, G f = 0) :=
  Variational.exists_energy_inverse (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (graphEnergy_coercive A J α hs ht)
    (energyInclusion_compact A J α hs ht D hD)

end TamingCompatibility.GeometricHilbert

end

end OAI
