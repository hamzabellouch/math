import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.CriticalInverse

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

include hD in

lemma geometric_scaled_source_dual (p : A.centers) (τ : 𝓢(Space,ℝ)) {V : Set Space}
    (hV : IsCompact V) (hVD : V ⊆ (D p).domain)
    (hτ : ∀ z ∈ V, τ z * coordinateWeight A p z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : 𝓢(Space,ℝ))
      (hc : HasCompactSupport (φ : Space → ℝ)) (hφV : tsupport φ ⊆ V)
      (j : Fin 2) (q : Space) (r M : ℝ), 0 ≤ r → 0 ≤ M →
      tsupport φ ⊆ Metric.ball q r → (∀ x, |φ x| ≤ M) →
      ∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true
          (testAnti A J α hs ht D p (componentTest j φ)
            (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφV.trans hVD))).val,
          energyInclusion A J α hs ht v⟫| ≤ (C*M*r^3)*‖v‖ := by
  obtain ⟨B,hB,hpair⟩ := critical_chart_pairing A J α hs ht D hD p τ hVD hτ
  obtain ⟨K,hK,hscale⟩ := densityTest_scale_bound A J α hs ht D p hV hVD
  refine ⟨B*K,mul_nonneg hB hK,fun φ hc hφV j q r M hr hM hball hb v => ?_⟩
  apply (hpair φ hc hφV j v).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hscale φ hc hφV q r M hr hM hball hb) hB) (norm_nonneg v)
  simpa only [mul_assoc] using h

include hD in

theorem geometric_smooth_dual_inverse :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      (∀ f v, ⟪weakDelta A J α hs ht (G f),weakDelta A J α hs ht v⟫ =
        ⟪f-(harmonicAnti A J α hs ht).starProjection f,energyInclusion A J α hs ht v⟫) ∧
      (∀ f, energyInclusion A J α hs ht (G f) ∈ (harmonicAnti A J α hs ht)ᗮ) ∧
      (∀ f : antiPre A J α hs ht, ∃ a : antiPre A J α hs ht,
        antiToEnergy A J α hs ht a = G (smoothL2 A J α hs ht true f.val)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f M, 0 ≤ M →
        (∀ v : antiEnergy A J α hs ht,
          |⟪f,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) → ‖G f‖ ≤ C*M := by
  obtain ⟨-,G,hweak,horth,-,hsm⟩ := geometric_smooth_inverse A J α hs ht D hD
  refine ⟨G,hweak,horth,hsm,1+(‖weakDelta A J α hs ht‖*‖G‖)^2,by positivity,?_⟩
  intro f M hM hb
  apply Variational.energy_inverse_dual_bound (energyInclusion A J α hs ht)
    (weakDelta A J α hs ht) (harmonicAnti A J α hs ht) G _ hweak horth f M hM hb
  intro u
  exact WithLp.prod_norm_sq_eq_of_L2 u.val
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hD in

lemma exists_smooth_inverse_dual_data :
    ∃ G : L2 A J α hs ht true →L[ℝ] antiEnergy A J α hs ht,
      ∃ H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht,
        (∀ f, smoothL2 A J α hs ht true (H f).val =
          (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val)) ∧
        (∀ f, IsClosed (H f).val.val) ∧
        (∀ f, antiToEnergy A J α hs ht (Gs f) = G (smoothL2 A J α hs ht true f.val)) ∧
        (∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
            weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
          (∀ v : antiEnergy A J α hs ht,
            |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
          ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ C*M := by
  classical
  let i : antiPre A J α hs ht →ₗ[ℝ] L2 A J α hs ht true :=
    (smoothL2 A J α hs ht true).toLinearMap.comp (antiPre A J α hs ht).subtype
  have hi : Function.Injective i := (smoothL2 A J α hs ht true).injective.comp Subtype.val_injective
  let j := (harmonicAnti A J α hs ht).starProjection.toLinearMap.comp i
  have hH : ∀ f, ∃ h : antiPre A J α hs ht, i h = j f := by
    intro f
    obtain ⟨h,hh,-⟩ := harmonicAnti_smooth A J α hs ht D hD (j f)
      ((harmonicAnti A J α hs ht).starProjection_apply_mem (i f))
    exact ⟨h,hh⟩
  let H := InjectiveLinearLift.lift i hi j hH
  have hHspec (f) : i (H f) = j f := InjectiveLinearLift.lift_spec i hi j hH f
  have hHclosed (f) : IsClosed (H f).val.val := by
    obtain ⟨h,hh,hc⟩ := harmonicAnti_smooth A J α hs ht D hD (j f)
      ((harmonicAnti A J α hs ht).starProjection_apply_mem (i f))
    have he : H f = h := hi ((hHspec f).trans hh.symm)
    rw [he]
    exact coclosed_antiInvariant_closed J α ht h.val.property h.property hc
  obtain ⟨G,hG,-,hGs,C,hC,hdual⟩ := geometric_smooth_dual_inverse A J α hs ht D hD
  have hanti : Function.Injective (antiToEnergy A J α hs ht) := by
    intro a b hab
    apply hi
    exact congrArg (energyInclusion A J α hs ht) hab
  let Gs := InjectiveLinearLift.lift (antiToEnergy A J α hs ht) hanti (G.toLinearMap.comp i) hGs
  have hGspec (f) : antiToEnergy A J α hs ht (Gs f) = G (i f) :=
    InjectiveLinearLift.lift_spec (antiToEnergy A J α hs ht) hanti (G.toLinearMap.comp i) hGs f
  refine ⟨G,H,Gs,hHspec,hHclosed,hGspec,?_,C,hC,?_⟩
  · intro f v
    rw [hGspec,hG]
    change ⟪i f - j f,energyInclusion A J α hs ht v⟫ =
      ⟪i (f-H f),energyInclusion A J α hs ht v⟫
    rw [map_sub,hHspec]
  · intro f M hM hb
    rw [hGspec]
    exact hdual (i f) M hM hb

end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
