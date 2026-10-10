import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.NormalizedHarmonicRHS
import OAI.Geometry.TamingCompatibility.DifferentialForms.RawPairLinear

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

theorem geometric_off_source_two_jet (p : A.centers) (τ ρ : 𝓢(Space,ℝ))
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
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (hr : 0 < t.1),
      t.1 ≤ 1 → ∀ (f h a : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      (∀ v : antiEnergy A J α hs ht,
        |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
      (∃ O : Set Space, IsOpen O ∧ O ⊆ W ∧
        (∀ n ≤ 3, tsupport (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1))) ⊆ O) ∧
        ∀ z ∈ O, rawPair J α ht p.val (D p) f.val.val z = 0) →
      (∀ v : antiEnergy A J α hs ht,
        ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true (f-h).val,energyInclusion A J α hs ht v⟫) →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ η a)
      ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
        C₀*(M*t.1^3 + ‖antiToEnergy A J α hs ht a‖) := by
  obtain ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C,hC,hest⟩ :=
    geometric_center_local_energy_two_jet A J α hs ht D hD p τ hU hUD hτ q hq ζ hζ χ hcχ hχ hζχ
  obtain ⟨K,hK,harm⟩ := normalized_harmonic_rhs_bound A J α hs ht D hD p τ ρ L 3
  refine ⟨W,V,hW,hqW,hWU,hV,hqV,hVW,η,hη,hηone,L,C*(K+1),by positivity,?_⟩
  filter_upwards [hest] with t hh
  intro hr hr1 f h a M hM hproj hdual hzero heq
  obtain ⟨O,hO,hOW,hχO,hfO⟩ := hzero
  let g := -weightedRawRHS A J α hs ht D hD p τ ρ h
  have hg : ∀ z ∈ O, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f-h).val.val z := by
    intro z hz
    change -(weightedRawRHS A J α hs ht D hD p τ ρ h z) = _
    rw [weightedRawRHS_spec A J α hs ht D hD p τ ρ h (hUD (hWU (hOW hz)))
      (hτ z (hWU (hOW hz))) (hρ z (hWU (hOW hz)))]
    change _ = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) (f.val.val-h.val.val) z
    rw [rawPair_sub,hfO z hz,zero_sub,smul_neg]
  have hd : ∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ ≤ (K*M)/t.1^k := by
    intro k hk v hv x
    have hb := harm f h hproj M hM hdual k hk v hv x
    have he : ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) g))) x‖ =
      ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (SchwartzMap.postcompCLM (embed 2) (weightedRawRHS A J α hs ht D hD p τ ρ h)))) x‖ := by
      simp only [g,map_neg,LineDeriv.iteratedLineDerivOp_neg,neg_apply,norm_neg]
    rw [he]
    apply hb.trans
    apply (le_div_iff₀ (pow_pos hr k)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr1) (mul_nonneg hK hM)
  have hb := hh hr (f-h) a g (K*M) (mul_nonneg hK hM)
    ⟨O,hO,hOW,hχO,hg⟩ hd heq
  dsimp only
  intro x hx
  apply (hb x hx).trans
  have hm : 0 ≤ M*t.1^3 := mul_nonneg hM (pow_nonneg hr.le _)
  nlinarith [norm_nonneg (antiToEnergy A J α hs ht a),mul_nonneg hC hm,
    mul_nonneg hK (norm_nonneg (antiToEnergy A J α hs ht a))]
end TamingCompatibility.GeometricHilbert

end

end OAI
