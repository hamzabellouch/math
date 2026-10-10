import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ClosedLiftBasisBound
import OAI.Geometry.TamingCompatibility.Hodge.HarmonicDualBound
import OAI.Geometry.TamingCompatibility.Charts.LocalDDStarEstimate

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def normalizedRawRHSMap (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (L : Space ≃L[ℝ] Space) :
    antiPre A J α hs ht →ₗ[ℝ] 𝓢(Space,C 2) :=
  (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm).restrictScalars ℝ).toLinearMap.comp
    (SchwartzMap.postcompCLM (embed 2)).toLinearMap).comp
      ((2:ℝ) • (SchwartzMap.smulLeftCLM EuclideanEnergy.Pair ρ).toLinearMap.comp
        ((SchwartzMap.smulLeftCLM EuclideanEnergy.Pair τ).toLinearMap.comp
          ((SchwartzMap.postcompCLM (retract 2)).toLinearMap.comp
            ((pairLinear A J α ht D hD p).comp (antiPre A J α hs ht).subtype))))

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma normalizedRawRHSMap_apply (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (L : Space ≃L[ℝ] Space)
    (f : antiPre A J α hs ht) :
    normalizedRawRHSMap A J α hs ht D hD p τ ρ L f =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ f)) := rfl

include hD in

lemma normalized_harmonic_rhs_bound (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    (L : Space ≃L[ℝ] Space) (N : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      ∀ n ≤ N, ∀ v : Fin n → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ h)))) x‖ ≤ C₀*M := by
  obtain ⟨C₀,hC,hb⟩ := harmonic_schwartz_dual_derivative_bound A J α hs ht D hD
    (normalizedRawRHSMap A J α hs ht D hD p τ ρ L) N
  exact ⟨C₀,hC,by simpa only [normalizedRawRHSMap_apply] using hb⟩
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

theorem geometric_inhomogeneous_two_jet (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (_hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (f h a : antiPre A J α hs ht) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L f)) x‖ ≤ N/t.1^k) →
      (∀ v : antiEnergy A J α hs ht,
        ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-h).val,energyInclusion A J α hs ht v⟫) →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ η a)
      ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
        C₀*((N+M)*t.1^3 + ‖antiToEnergy A J α hs ht a‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_center_energy_two_jet A J α hs ht D hD p τ hU hUD hτ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨K,hK,harm⟩ := normalized_harmonic_rhs_bound A J α hs ht D hD p τ ρ L 3
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C*(K+1),by positivity,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 f h a M N hM hN hproj hdual hsource heq
  let g := weightedRawRHS A J α hs ht D hD p τ ρ (f-h)
  have hg : ∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f-h).val.val z := by
    intro z hz
    exact weightedRawRHS_spec A J α hs ht D hD p τ ρ (f-h) (hUD (hWU hz)) (hτ z (hWU hz)) (hρ z (hWU hz))
  have hd : ∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ ≤ (N+K*M)/t.1^k := by
    intro k hk v hv x
    have hb := harm f h hproj M hM hdual k hk v hv x
    have hharm : ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L h)) x‖ ≤ K*M/t.1^k := by
      apply hb.trans
      apply (le_div_iff₀ (pow_pos hr k)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1) (mul_nonneg hK hM)
    change ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L (f-h))) x‖ ≤ _
    rw [map_sub]
    rw [sub_eq_add_neg,LineDeriv.iteratedLineDerivOp_add,LineDeriv.iteratedLineDerivOp_neg]
    simp only [← sub_eq_add_neg]
    calc
      _ ≤ ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L f)) x‖ +
          ‖(∂^{v} (normalizedRawRHSMap A J α hs ht D hD p τ ρ L h)) x‖ := norm_sub_le _ _
      _ ≤ N/t.1^k + K*M/t.1^k := add_le_add (hsource k hk v hv x) hharm
      _ = (N+K*M)/t.1^k := by rw [add_div]
  have hb := hh hr (f-h) a g (N+K*M) (by positivity) hg hd heq
  dsimp only
  intro x hx
  apply (hb x hx).trans
  have hr3 := pow_nonneg hr.le 3
  have hsum := add_nonneg hN hM
  have hn : 0 ≤ N*t.1^3 := mul_nonneg hN hr3
  have hm : 0 ≤ M*t.1^3 := mul_nonneg hM hr3
  nlinarith [norm_nonneg (antiToEnergy A J α hs ht a),mul_nonneg hC hm,
    mul_nonneg hC hn,mul_nonneg hK (norm_nonneg (antiToEnergy A J α hs ht a)),mul_nonneg hK hn]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
