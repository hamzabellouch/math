import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.InteriorEstimateApply
import OAI.Geometry.TamingCompatibility.Charts.SquareCutoff

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma actual_localized_square_source (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    {q : Space} (d : SquareData A J α ht D p U q)
    (η χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχ : tsupport χ ⊆ d.W)
    (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1)
    (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ d.W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (heq : ∀ v : antiEnergy A J α hs ht,
      ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
        ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    smulLeftCLM (C 2) χ (square EuclideanEnergy.e d.a d.b d.ρ
      (localizedRawSchwartz A J α hs ht D hD p τ η a : 𝓢'(Space,C 2))) =
    smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
  rw [localizedRawSchwartz_spec]
  rw [square_cutoff_locality EuclideanEnergy.e d.a d.b d.ρ d.g d.polarized χ η hη
    (rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht a))]
  exact raw_square_source A J α hs ht D hD p τ d.openW (d.WU.trans hUD)
    (fun z hz => hτ z (d.WU hz)) d.a d.b d.ρ d.agreeA d.agreeB d.agreeρ
    f (antiToEnergy A J α hs ht a) heq g hg χ hc hχ

lemma actual_localized_square_source_on (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    {q : Space} (d : SquareData A J α ht D p U q)
    {O : Set Space} (hO : IsOpen O) (hOW : O ⊆ d.W)
    (η χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) (hχ : tsupport χ ⊆ O)
    (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1)
    (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair))
    (hg : ∀ z ∈ O, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z)
    (heq : ∀ v : antiEnergy A J α hs ht,
      ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
        ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) :
    smulLeftCLM (C 2) χ (square EuclideanEnergy.e d.a d.b d.ρ
      (localizedRawSchwartz A J α hs ht D hD p τ η a : 𝓢'(Space,C 2))) =
    smulLeftCLM (C 2) χ (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
  rw [localizedRawSchwartz_spec]
  rw [square_cutoff_locality EuclideanEnergy.e d.a d.b d.ρ d.g d.polarized χ η hη
    (rawDistribution A J α hs ht D hD p τ (antiToEnergy A J α hs ht a))]
  exact raw_square_source A J α hs ht D hD p τ hO (hOW.trans (d.WU.trans hUD))
    (fun z hz => hτ z (d.WU (hOW hz))) d.a d.b d.ρ
    (fun z hz => d.agreeA z (hOW hz)) (fun z hz => d.agreeB z (hOW hz))
    (fun z hz => d.agreeρ z (hOW hz))
    f (antiToEnergy A J α hs ht a) heq g hg χ hc hχ

end TamingCompatibility.GeometricHilbert

end

end OAI
