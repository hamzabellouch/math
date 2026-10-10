import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.InverseCutoff
import OAI.Geometry.TamingCompatibility.Functional.WeakNormalEquation

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open Set Filter MeasureTheory ComplexMatrix
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exists_patch (p : A.centers) {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    {z : Space} (hz : z ∈ U) (g : Space →ᵇ C 2) (hg : ContDiff ℝ ∞ (g : Space → C 2)) :
    ∃ W : Set Space, IsOpen W ∧ z ∈ W ∧ W ⊆ U ∧ ∃ w : antiPre A J α hs ht,
      ∀ y ∈ W, rawPair J α ht p.val (D p) w.val.val y = retract 2 (g y) := by
  obtain ⟨η,hc,hηU,W,hW,hzW,hWU,hη⟩ := SchwartzCutoff.exists_one_near hU hz
  let q : Space → EuclideanEnergy.Pair := fun y => η y • retract 2 (g y)
  have hq : ContDiff ℝ ∞ q := (η.smooth ⊤).smul ((retract 2).contDiff.comp hg)
  have hqs : tsupport q ⊆ tsupport η := tsupport_smul_subset_left _ _
  have hqc : HasCompactSupport q := hc.of_isClosed_subset (isClosed_tsupport q) hqs
  let ψ := hqc.toSchwartzMap hq
  let w := testAnti A J α hs ht D p ψ hqc (hqs.trans (hηU.trans hUD))
  refine ⟨W,hW,hzW,hWU,w,fun y hy => ?_⟩
  change rawPair J α ht p.val (D p) (manifoldTest J α ht p.val (D p) q) y = _
  rw [rawPair_manifoldTest J α ht p.val (D p) (hqs.trans (hηU.trans hUD)) (hUD (hWU hy))]
  change η y • retract 2 (g y) = _
  rw [hη y hy,one_smul]

end TamingCompatibility.GeometricHilbert

end

end OAI
