import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RawRepresentative
import OAI.Geometry.TamingCompatibility.Functional.LocalPatchConstruction
import OAI.Geometry.TamingCompatibility.Charts.LocalSmoothPairing
import OAI.Geometry.TamingCompatibility.DifferentialForms.TestLinear
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiSmoothMultiply

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma exists_weak_patch (f : antiPre A J α hs ht) (u : antiEnergy A J α hs ht)
    (heq : ∀ v : antiEnergy A J α hs ht, ⟪weakDelta A J α hs ht u,weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : antiPre A J α hs ht,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : antiPre A J α hs ht,
          ⟪energyInclusion A J α hs ht u,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ =
          ⟪smoothL2 A J α hs ht true w.val,smoothL2 A J α hs ht true (antiMultiply A J α hs ht ρ hρ a).val⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht D hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,U,hU,hxU,hUD,hτ,g,hgs,hgd⟩ := raw_smooth_near A J α hs ht D hD p
    (extChartAt Model p.val x) hxp hw f u heq
  obtain ⟨W,hW,hxW,hWU,w,hw⟩ := exists_patch A J α hs ht D p hU hUD hxU g hgs
  let V := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hV : IsOpen V := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨V,hV,⟨hxs,hxW⟩,w,fun ρ hρ hρV a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := supported_anti_test A J α hs ht D p hW (hWU.trans hUD) ρ hρ hρV a
  rw [← hq]
  refine pair_all_tests_eq A J α hs ht D p (hWU.trans hUD) _ _ ?_ q hqc hqW
  intro φ hc hφW j
  exact local_pairing_eq A J α hs ht D hD p τ (hWU.trans hUD)
    (fun z hz => hτ z (hWU hz)) u g (fun χ hc hχ => hgd χ hc (hχ.trans hWU))
    w hw φ hc hφW j

end TamingCompatibility.GeometricHilbert

end

end OAI
