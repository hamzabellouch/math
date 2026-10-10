import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.SmoothCorrection
import OAI.Geometry.TamingCompatibility.Hodge.HodgeProjectionRaw
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairing

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ComplexMatrix GeometricChart
open TemperedDistribution EuclideanSobolevOperators HilbertSobolev Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in

lemma hodge_antiRHS_bound (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (U : Set Space) (hχ : ∀ z ∈ U, χ z = 1) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 3,
        (∀ f, toDistribution Space (C 6) 3 (L f) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
        ∀ f, ‖L f‖ ≤ B*(r⁻¹)^3*‖f‖)
    (ρ : 𝓢(Space,ℝ)) (hρ : tsupport ρ ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ a : PreL2 A J α hs ht true,
        ‖schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
          (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
            (smoothAntiProjection A J α hs ht a)))‖ ≤
          C₀*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  let ρc := SchwartzMap.postcompCLM Complex.ofRealCLM ρ
  let M := antiPairSelector.comp antiMatrix
  let N : H Space (C 6) 3 →L[ℂ] H Space (C 2) 3 :=
    (2:ℂ) • (product 3 ρc).comp (fiberOperator 3 M)
  refine ⟨‖N‖*B,mul_nonneg (norm_nonneg _) hB,fun r hr hr1 a => ?_⟩
  obtain ⟨L,he,hb⟩ := hL r hr hr1
  let f := smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)
  have hsupp : tsupport ρc ⊆ U :=
    (tsupport_comp_subset (map_zero Complex.ofRealCLM) ρ).trans hρ
  have hdist : toDistribution Space (C 2) 3 (N (L f)) =
      (SchwartzMap.postcompCLM (embed 2)
        (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
          (smoothAntiProjection A J α hs ht a)) : 𝓢'(Space,C 2)) := by
    rw [weightedRawRHS_full_distribution]
    change toDistribution Space (C 2) 3 (N (L f)) =
      (2:ℂ) • smulLeftCLM (C 2) ρc (fiberMap antiPairSelector
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeSmooth A J α hs ht (preAntiProjection A J α hs ht a))))
    rw [preAntiProjection_apply,hodgeRawDistribution_smooth_antiInvariant]
    simp only [N,smul_apply,ContinuousLinearMap.comp_apply,map_smul]
    have hp (u : H Space (C 2) 3) : toDistribution Space (C 2) 3 (product 3 ρc u) =
        smulLeftCLM (C 2) ρc (toDistribution Space (C 2) 3 u) := by
      simpa only [Nat.cast_ofNat] using toDistribution_product (F := C 2) 3 ρc u
    have hef := he f
    dsimp only [f] at hef
    rw [hodgeRegularizedGraph_smoothShift_cube] at hef
    rw [hp,toDistribution_fiberOperator,hef,fiberMap_product]
    rw [local_cutoff_one χ ρc (fun z hz => hχ z (hsupp hz))]
    congr 2
  have hn : schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
      (weightedRawRHS A J α hs ht (fun p => (D p).toData) hD p τ ρ
        (smoothAntiProjection A J α hs ht a))) = N (L f) := by
    apply toDistribution_injective (3:ℝ)
    rw [schwartzToH_spec,hdist]
  rw [hn]
  calc
    _ ≤ ‖N‖*‖L f‖ := N.le_opNorm _
    _ ≤ ‖N‖*(B*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left (hb f) (norm_nonneg _)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume GeometricAdjoint
open Set ComplexMatrix HilbertSobolev
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def rawRHSSeminormMap (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) :
    antiPre A J α hs ht →ₗ[ℝ] H Space ScalarPair.F (3:ℝ) :=
  ((schwartzToH (3:ℝ)).restrictScalars ℝ).toLinearMap.comp
    ((SchwartzMap.postcompCLM (embed 2)).toLinearMap.comp
      ((2:ℝ) • (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ).toLinearMap.comp
        ((SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ).toLinearMap.comp
          ((SchwartzMap.postcompCLM (retract 2)).toLinearMap.comp
            ((pairLinear A J α ht D hD p).comp (antiPre A J α hs ht).subtype)))))

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma rawRHSSeminormMap_apply (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (f : antiPre A J α hs ht) :
    rawRHSSeminormMap A J α hs ht D hD p τ ρ f =
      schwartzToH (3:ℝ) (SchwartzMap.postcompCLM (embed 2)
        (weightedRawRHS A J α hs ht D hD p τ ρ f)) := rfl

end TamingCompatibility.GeometricHilbert

end
end

section
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

include hD in

lemma exists_local_ddstar_estimate_on (p : A.centers) (τ : 𝓢(Space,ℝ))
    (U : Set Space) (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hqU : q ∈ U) :
    ∃ ρ : 𝓢(Space,ℝ), HasCompactSupport (ρ : Space → ℝ) ∧ tsupport ρ ⊆ U ∧
    ∃ O : Set Space, IsOpen O ∧ q ∈ O ∧ O ⊆ (D p).domain ∧
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
  have hρsupp : tsupport ρ ⊆ U :=
    (tsupport_smul_subset_left (ζ : Space → ℝ) (fun z => chartDensity J α p.val z)).trans hζU
  have hρcomp : HasCompactSupport (ρ : Space → ℝ) :=
    hζ.of_isClosed_subset (isClosed_tsupport ρ)
      (tsupport_smul_subset_left (ζ : Space → ℝ) (fun z => chartDensity J α p.val z))
  refine ⟨ρ,hρcomp,hρsupp,O,hO,hqO,hOO₀.trans (hO₀V.trans (hVW.trans (hWU₀.trans (hU₀U.trans hUD)))),
    C,hC,fun f a heq x hx => ?_⟩
  have hxK : x ∈ tsupport η := subset_closure (by simpa only [Function.mem_support,hηone x hx] using one_ne_zero)
  exact hbound f a (weightedRawRHS A J α hs ht D hD p τ ρ f)
    (fun z hz => weightedRawRHS_spec A J α hs ht D hD p τ ρ f
      (hUD (hU₀U (hWU₀ hz))) (hτ z (hU₀U (hWU₀ hz))) (hρ z (hWU₀ hz))) heq x hxK

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
