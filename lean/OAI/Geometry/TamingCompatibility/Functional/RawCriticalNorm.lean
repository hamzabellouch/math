import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.InteriorEstimateApply

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolevOperators
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
local instance : Fact ((1 : ENNReal) ≤ 4) := ⟨by norm_num⟩

lemma localizedRawSchwartz_H1 (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) :
    schwartzToH 1 (localizedRawSchwartz A J α hs ht D hD p τ χ a) =
      product 1 χ (rawH1 A J α hs ht D hD p τ (antiToEnergy A J α hs ht a)) := by
  apply toDistribution_injective 1
  rw [schwartzToH_spec,localizedRawSchwartz_spec]
  have h := toDistribution_product (E := Space) (F := C 2) 1 χ
    (rawH1 A J α hs ht D hD p τ (antiToEnergy A J α hs ht a))
  have hraw := rawH1_spec A J α hs ht D hD p τ (antiToEnergy A J α hs ht a)
  simp only [toDistribution,Nat.cast_one] at h hraw ⊢
  rw [hraw] at h
  exact h.symm

omit [MeasurableSpace X] [BorelSpace X] in
lemma localizedRawSchwartz_compact (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (hc : HasCompactSupport (χ : Space → ℂ)) (a : antiPre A J α hs ht) :
    HasCompactSupport (localizedRawSchwartz A J α hs ht D hD p τ χ a : Space → C 2) := by
  have he : (localizedRawSchwartz A J α hs ht D hD p τ χ a : Space → C 2) =
      (χ : Space → ℂ) • (SchwartzMap.postcompCLM (embed 2)
        (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ (realPairSchwartz A J α ht D hD p a.val)) : Space → C 2) := by
    funext x
    exact SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth _ x
  rw [he]
  exact hc.smul_right

lemma localizedRawSchwartz_H1_bound (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (a : antiPre A J α hs ht) :
    ‖schwartzToH 1 (localizedRawSchwartz A J α hs ht D hD p τ χ a)‖ ≤
      (‖product (F := C 2) 1 χ‖ * ‖rawH1 A J α hs ht D hD p τ‖) *
        ‖antiToEnergy A J α hs ht a‖ := by
  rw [localizedRawSchwartz_H1]
  apply ((product (F := C 2) 1 χ).le_opNorm _).trans
  have h := mul_le_mul_of_nonneg_left
    ((rawH1 A J α hs ht D hD p τ).le_opNorm (antiToEnergy A J α hs ht a))
    (norm_nonneg (product (F := C 2) 1 χ))
  simpa only [mul_assoc] using h

lemma raw_critical_norm (p : A.centers) (τ : 𝓢(Space,ℝ)) (χ : 𝓢(Space,ℂ))
    (hc : HasCompactSupport (χ : Space → ℂ)) (L : Space ≃L[ℝ] Space) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : antiPre A J α hs ht,
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ χ a)
      ‖u.toLp 4 (volume : Measure Space)‖ +
        ∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u).toLp 2 (volume : Measure Space)‖ ≤
          K * ‖antiToEnergy A J α hs ht a‖ := by
  obtain ⟨B,hB,hbound⟩ := critical_linear_H1 (F := C 2)
    (by simp [Space] : Module.finrank ℝ Space = 4) L
  let K := ‖product (F := C 2) 1 χ‖ * ‖rawH1 A J α hs ht D hD p τ‖
  refine ⟨B*K,by dsimp [K]; positivity,fun a => ?_⟩
  dsimp only
  have hb := hbound (localizedRawSchwartz A J α hs ht D hD p τ χ a)
    (localizedRawSchwartz_compact A J α hs ht D hD p τ χ hc a)
  have hk := localizedRawSchwartz_H1_bound A J α hs ht D hD p τ χ a
  apply hb.trans
  have h := mul_le_mul_of_nonneg_left hk hB
  simpa only [mul_assoc,K] using h
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
