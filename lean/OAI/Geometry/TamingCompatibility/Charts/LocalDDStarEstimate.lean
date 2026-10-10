import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricScaledJet

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def weightedRawRHS (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) : 𝓢(Space,EuclideanEnergy.Pair) :=
  (2:ℝ) • SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ
    (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p f.val))

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma weightedRawRHS_spec (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) {z : Space} (hz : z ∈ (D p).domain)
    (hτ : τ z * coordinateWeight A p z = 1) (hρ : ρ z = chartDensity J α p.val z) :
    weightedRawRHS A J α hs ht D hD p τ ρ f z =
      (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z := by
  simp only [weightedRawRHS,smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ρ.hasTemperateGrowth,
    cutoff_realPair_raw A J α ht D hD p f.val τ hz hτ,hρ,smul_smul]

include hD in

lemma exists_local_ddstar_estimate (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ ρ : 𝓢(Space,ℝ), ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (f a : antiPre A J α hs ht),
        (∀ v : antiEnergy A J α hs ht,
          ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
            ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
        ∀ x ∈ O,
          ‖ManifoldForms.pullback (exteriorDerivative (codifferential J α ht a.val.val))
            (extChartAt Model p.val).symm x‖ ≤
            C * (‖antiToEnergy A J α hs ht a‖ +
              ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
                (weightedRawRHS A J α hs ht D hD p τ ρ f))‖) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨ζ,hζ,hζU,U₀,hU₀,hqU₀,hU₀U,hζone⟩ := SchwartzCutoff.exists_one_near hU hqU
  let ρ : 𝓢(Space,ℝ) := SchwartzCutoff.schwartz (D p).domain_open
    ((chartDensity_smooth J α hs ht p.val).mono (D p).domain_subset)
    (ζ.smooth ⊤) hζ (hζU.trans hUD)
  have hρ (z) (hz : z ∈ U₀) : ρ z = chartDensity J α p.val z := by
    simp only [ρ,SchwartzCutoff.schwartz_apply,hζone z hz,one_smul]
  obtain ⟨W,V,hW,hqW,hWU₀,hV,hqV,hVW,hest⟩ :=
    ddstar_coordinate_estimate A J α hs ht D hD p τ hU₀ (hU₀U.trans hUD)
      (fun z hz => hτ z (hU₀U hz)) q hqU₀
  obtain ⟨χ₀,hχ₀,hχ₀V,O₀,hO₀,hqO₀,hO₀V,hχone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM χ₀
  have hχs : tsupport χ ⊆ tsupport χ₀ := tsupport_comp_subset (map_zero Complex.ofRealCLM) χ₀
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hχ₀.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχ (z) (hz : z ∈ O₀) : χ z = 1 := by
    simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hχone z hz,Complex.ofReal_one]
  obtain ⟨η,hη,hηO₀,O,hO,hqO,hOO₀,hηone⟩ := SchwartzCutoff.exists_one_near hO₀ hqO₀
  obtain ⟨C,hC,hbound⟩ := hest χ hχc (hχs.trans hχ₀V) O₀ (tsupport η)
    hO₀ hO₀V hχ hη hηO₀
  refine ⟨τ,ρ,O,hO,hqO,hOO₀.trans (hO₀V.trans (hVW.trans (hWU₀.trans (hU₀U.trans hUD)))),
    C,hC,fun f a heq x hx => ?_⟩
  have hxK : x ∈ tsupport η := subset_closure (by simpa only [Function.mem_support,hηone x hx] using one_ne_zero)
  exact hbound f a (weightedRawRHS A J α hs ht D hD p τ ρ f)
    (fun z hz => weightedRawRHS_spec A J α hs ht D hD p τ ρ f
      (hUD (hU₀U (hWU₀ hz))) (hτ z (hU₀U (hWU₀ hz))) (hρ z (hWU₀ hz))) heq x hxK

end TamingCompatibility.GeometricHilbert

end

end OAI
