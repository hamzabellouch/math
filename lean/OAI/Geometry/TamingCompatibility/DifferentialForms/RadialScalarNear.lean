import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScaledNearData
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialRHSIdentification

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

lemma exists_rhs_scalarJet_constant (L : Space ≃L[ℝ] Space) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Fin 2, ∀ k ≤ N,
      ‖(2:ℝ) • complexComponentCLM j‖ * ‖L.symm.toContinuousLinearMap‖^k ≤ C := by
  classical
  let a := fun (j : Fin 2) (k : ℕ) => ‖(2:ℝ) • complexComponentCLM j‖ * ‖L.symm.toContinuousLinearMap‖^k
  have hn : ∀ j k, 0 ≤ a j k := fun j k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  refine ⟨1 + ∑ j : Fin 2, ∑ k ∈ Finset.range (N+1), a j k,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hn j k)))
  · intro j k hk
    have h1 : a j k ≤ ∑ k ∈ Finset.range (N+1), a j k :=
      Finset.single_le_sum (fun i _ => hn j i) (Finset.mem_range.mpr (by omega))
    have h2 : (∑ k ∈ Finset.range (N+1), a j k) ≤ ∑ j : Fin 2, ∑ k ∈ Finset.range (N+1), a j k :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun k _ => hn i k)) (Finset.mem_univ j)
    exact (h1.trans h2).trans (le_add_of_nonneg_left (by norm_num))

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_component_scaled_bound (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (N : ℕ) (C : ℝ)
    (hC : ∀ j : Fin 2, ∀ k ≤ N, ‖(2:ℝ) • complexComponentCLM j‖ * ‖L.symm.toContinuousLinearMap‖^k ≤ C)
    (j : Fin 2) (φ : 𝓢(Space,ℝ))
    (hc : HasCompactSupport (φ : Space → ℝ)) (hφD : tsupport φ ⊆ (D p).domain)
    (hτ : ∀ z ∈ tsupport φ, τ z * coordinateWeight A p z = 1)
    (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hjets : ∀ k ≤ N, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ z) z‖ ≤ M/r^k) :
    ∀ k ≤ N, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
    ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L
      (testAnti A J α hs ht D p (componentTest j φ) (componentTest_compact j φ hc)
        ((componentTest_support j φ).trans hφD)))) x‖ ≤ C*M/r^k := by
  intro k hk v hv x
  calc
    _ ≤ ‖(2:ℝ) • complexComponentCLM j‖ *
        ‖iteratedFDeriv ℝ k (fun z => ρ z * φ z) (L.symm x)‖ * ‖L.symm.toContinuousLinearMap‖^k :=
      normalizedRawRHSMap_component_derivative_le A J α hs ht D hD p τ ρ L j φ hc hφD hτ k v hv x
    _ ≤ ‖(2:ℝ) • complexComponentCLM j‖ * (M/r^k) * ‖L.symm.toContinuousLinearMap‖^k := by
      gcongr
      exact hjets k hk (L.symm x)
    _ = (‖(2:ℝ) • complexComponentCLM j‖ * ‖L.symm.toContinuousLinearMap‖^k)*M/r^k := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hC j k hk) hM)
      (pow_nonneg hr.le k)

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

include hD hH hweak hB hdual in

theorem closedLift_scalar_near_source
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1)
    (hχ0 : ((χ 4 : Space → ℂ) =ᶠ[𝓝 0] fun _ => 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (_hr : 0 < t.1), t.1 ≤ 1 →
      ∀ (φ : 𝓢(Space,ℝ)) (hc : HasCompactSupport (φ : Space → ℝ))
        (hφK : tsupport φ ⊆ K) (j : Fin 2) (b : Space) (M : ℝ), 0 ≤ M →
        tsupport φ ⊆ Metric.ball b t.1 → (∀ z, |φ z| ≤ M) →
        (∀ k ≤ 3, ∀ z, ‖iteratedFDeriv ℝ k (fun z => ρ z * φ z) z‖ ≤ M/t.1^k) →
        let f := testAnti A J α hs ht D p (componentTest j φ)
          (componentTest_compact j φ hc) ((componentTest_support j φ).trans (hφK.trans (hKU.trans hUD)))
        ‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
          (extChartAt Model p.val).symm t.2 -
          ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm t.2‖ ≤ C*M := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,he⟩ :=
    closedLift_scaled_near_source A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq ζ hζ χ hcχ hχ hζχ hχ0
  obtain ⟨c,hc,hce⟩ := exists_rhs_scalarJet_constant L 3
  refine ⟨C*c,mul_nonneg hC (le_trans (by norm_num) hc),?_⟩
  filter_upwards [he] with t htest
  intro hr hr1 φ hφc hφK j b M hM hball hval hjets
  dsimp only
  have hbound := htest hr hr1 φ hφc hφK j b (c*M) (mul_nonneg (le_trans (by norm_num) hc) hM) hball
    (fun z => (hval z).trans (by nlinarith))
    (normalizedRawRHSMap_component_scaled_bound A J α hs ht D hD p τ ρ L 3 c hce j φ hφc
      (hφK.trans (hKU.trans hUD)) (fun z hz => hτ z (hKU (hφK hz))) t.1 M hr hM hjets)
  simpa only [mul_assoc] using hbound

end TamingCompatibility.GeometricHilbert

end

end OAI
