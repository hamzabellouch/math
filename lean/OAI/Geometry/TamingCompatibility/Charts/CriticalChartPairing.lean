import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.CriticalManifoldSobolev
import OAI.Geometry.TamingCompatibility.DifferentialForms.CriticalHolder

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume ComplexMatrix
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩
local instance : Fact ((1 : ENNReal) ≤ ENNReal.ofReal (4/3:ℝ)) := ⟨by norm_num⟩

include hD in
lemma critical_chart_pairing (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ))
      (hc : HasCompactSupport (φ : Space → ℝ)) (hφU : tsupport φ ⊆ U)
      (j : Fin 2) (u : antiEnergy A J α hs ht),
      |⟪energyInclusion A J α hs ht
          (antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
            (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD)))),
        energyInclusion A J α hs ht u⟫| ≤
      C * ‖(densityTest A J α hs ht D p φ hc (hφU.trans hUD)).toLp
        (ENNReal.ofReal (4/3:ℝ)) (volume : Measure Space)‖ * ‖u‖ := by
  obtain ⟨C,hC,hbound⟩ := component_energy_L4_bound A J α hs ht D hD p
  let T := SchwartzMap.seminorm ℝ 0 0 τ
  have hT : 0 ≤ T := apply_nonneg _ _
  refine ⟨T*C,mul_nonneg hT hC,fun φ hc hφU j u => ?_⟩
  let ψ := densityTest A J α hs ht D p φ hc (hφU.trans hUD)
  let v := antiToEnergy A J α hs ht (testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφU.trans hUD)))
  change |⟪energyInclusion A J α hs ht v,energyInclusion A J α hs ht u⟫| ≤
    (T*C) * ‖ψ.toLp (ENNReal.ofReal (4/3:ℝ)) volume‖ * ‖u‖
  refine (antiToEnergy_dense A J α hs ht).induction_on u ?_ ?_
  · exact isClosed_le ((continuous_const.inner (energyInclusion A J α hs ht).continuous).abs)
      (continuous_const.mul continuous_norm)
  intro a
  have heq := smooth_raw_component_pair A J α hs ht D hD p τ hUD hτ φ hc hφU j a
  rw [rawDistribution_smooth,embedded_component_apply] at heq
  have heqr := Complex.ofReal_injective heq
  rw [real_inner_comm,← heqr]
  have hh := CriticalSobolev.schwartz_cutoff_holder_critical τ
    (realComponent (realPairSchwartz A J α ht D hD p a.val) j) ψ
  have hh' : |∫ x, ⟪(SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ
      (realPairSchwartz A J α ht D hD p a.val)) x,componentTest j ψ x⟫| ≤
      T * ‖(realComponent (realPairSchwartz A J α ht D hD p a.val) j).toLp 4 volume‖ *
        ‖ψ.toLp (ENNReal.ofReal (4/3:ℝ)) volume‖ := by
    simpa only [componentTest_inner,SchwartzMap.smulLeftCLM_apply_apply τ.hasTemperateGrowth,
      PiLp.smul_apply,smul_eq_mul,realComponent_apply] using hh
  refine hh'.trans ?_
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hbound a j) hT)
    (norm_nonneg (ψ.toLp (ENNReal.ofReal (4/3:ℝ)) volume))
  nlinarith only [hb]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
