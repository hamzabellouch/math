import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.NormalizedHarmonicRHS

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
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hH hweak hB hdual in

theorem geometric_scaled_near_source_of_data :
      ∀ (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
        (_hU : IsOpen U) (hUD : U ⊆ (D p).domain)
        (_hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
        (_hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
        (K : Set Space) (_hK : IsCompact K) (hKU : K ⊆ U)
        (q : Space) (_hq : q ∈ U)
        (ζ : 𝓢(Space,ℂ)) (_hζ : HasCompactSupport (ζ : Space → ℂ))
        (χ : ℕ → 𝓢(Space,ℂ)) (_hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
        (_hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
        (_hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1),
      ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (_hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (φ : 𝓢(Space,ℝ))
        (hc : HasCompactSupport (φ : Space → ℝ)) (hφK : tsupport φ ⊆ K)
        (j : Fin 2) (b : Space) (M : ℝ), 0 ≤ M →
        tsupport φ ⊆ Metric.ball b t.1 → (∀ z, |φ z| ≤ M) →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        (∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
          ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L f)) x‖ ≤ M/t.1^k) →
        let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
        ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
          t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
            t.1^3*∑ i, ∑ k, ‖(∂_{stdOrthonormalBasis ℝ Space k} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
          C*M*t.1^3 := by
  intro p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_inhomogeneous_two_jet A J α hs ht D hD p τ ρ hU hUD hτ hρ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨E,hE,hsource⟩ := geometric_scaled_source_dual A J α hs ht D hD p τ hK (hKU.trans hUD)
    (fun z hz => hτ z (hKU hz))
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C*(1+E+B*E),by positivity,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 φ hc hφK j b M hM hball hbound
  dsimp only
  intro hderiv
  let f := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
  have hd : ∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ E*M*t.1^3*‖v‖ :=
    hsource φ hc hφK j b t.1 M hr.le hM hball hbound
  have hEM : 0 ≤ E*M*t.1^3 := by positivity
  have ha := hdual f (E*M*t.1^3) hEM hd
  have hb := hh hr hr1 f (H f) (Gs f) (E*M*t.1^3) M hEM hM (hH f) hd hderiv (hweak f)
  intro x hx
  apply (hb x hx).trans
  calc
    C*((M+E*M*t.1^3)*t.1^3+‖antiToEnergy A J α hs ht (Gs f)‖) ≤
        C*(M*t.1^3+E*M*t.1^3+B*(E*M*t.1^3)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1 : t.1^3 ≤ 1) hEM
      nlinarith only [hp,ha]
    _ = C*(1+E+B*E)*M*t.1^3 := by ring
end TamingCompatibility.GeometricHilbert

end
end

section
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

variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hH hweak hB hdual in

theorem closedLift_scaled_near_source :
      ∀ (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
        (_hU : IsOpen U) (hUD : U ⊆ (D p).domain)
        (_hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
        (_hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
        (K : Set Space) (_hK : IsCompact K) (hKU : K ⊆ U)
        (q : Space) (_hq : q ∈ U)
        (ζ : 𝓢(Space,ℂ)) (_hζ : HasCompactSupport (ζ : Space → ℂ))
        (χ : ℕ → 𝓢(Space,ℂ)) (_hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
        (_hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
        (_hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
        (_hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)),
      ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (_hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (φ : 𝓢(Space,ℝ))
        (hc : HasCompactSupport (φ : Space → ℝ)) (hφK : tsupport φ ⊆ K)
        (j : Fin 2) (b : Space) (M : ℝ), 0 ≤ M →
        tsupport φ ⊆ Metric.ball b t.1 → (∀ z, |φ z| ≤ M) →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        (∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
          ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L f)) x‖ ≤ M/t.1^k) →
        ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
          (extChartAt Model p.val).symm t.2 -
          ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤
          C*M := by
  intro p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_scaled_near_source_of_data A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  have hKV : Metric.closedBall q (ε/2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεV
  obtain ⟨C₀,hC₀,hout⟩ := closedLift_scaled_basis_local_bound A J α hs ht D hD
    (stdOrthonormalBasis ℝ Space).toBasis p τ η L
    hV (hVW.trans (hWU.trans hUD))
    (fun z hz => hτ z (hWU (hVW hz))) hηone (isCompact_closedBall q (ε/2)) hKV
  have htK : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), t.2 ∈ Metric.closedBall q (ε/2) :=
    (continuous_snd.tendsto (0,q)).eventually (Metric.closedBall_mem_nhds q (by positivity))
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C₀*C,mul_nonneg hC₀ hC,?_⟩
  filter_upwards [hest,htK] with t hh htK
  intro hr hr1 φ hc hφK j b M hM hball hbound
  dsimp only
  intro hderiv
  let f := testAnti A J α hs ht D p (componentTest j φ)
    (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
  have hj := hh hr hr1 φ hc hφK j b M hM hball hbound hderiv 0 hχ0
  have ho := hout H Gs f t.2 htK t.1 (C*M*t.1^3) hr hr1 (by
    simpa only [smul_zero,zero_add,OrthonormalBasis.coe_toBasis] using hj)
  apply le_of_mul_le_mul_left (a := t.1^3) _ (pow_pos hr 3)
  calc
    _ ≤ C₀*(C*M*t.1^3) := ho
    _ = t.1^3*(C₀*C*M) := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
