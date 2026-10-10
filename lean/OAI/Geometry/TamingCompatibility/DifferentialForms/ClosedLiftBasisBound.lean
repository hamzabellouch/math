import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ShrinkingCutoff
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricScaledJet
import OAI.Geometry.TamingCompatibility.DifferentialForms.JetBasis

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart GeometricAdjoint Set ComplexMatrix
open scoped Manifold ContDiff RealInnerProductSpace SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in

lemma closedLift_scaled_basis_local_bound {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ Space) (p : A.centers) (τ : 𝓢(Space,ℝ)) (η : 𝓢(Space,ℂ))
    (L : Space ≃L[ℝ] Space) {U K : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1) (hη : ∀ z ∈ U, η z = 1)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
        (f : antiPre A J α hs ht) (z : Space), z ∈ K →
        ∀ (r M : ℝ), 0 < r → r ≤ 1 →
      (let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f))
       r*‖u (L z)‖ + r^2*∑ i, ‖(∂_{b i} u) (L z)‖ +
         r^3*∑ i, ∑ j, ‖(∂_{b j} (∂_{b i} u)) (L z)‖ ≤ M) →
      r^3*‖ManifoldForms.pullback (closedLiftOfInverse A J α hs ht H Gs f).val
        (extChartAt Model p.val).symm z -
        ManifoldForms.pullback (k := 2) (H f).val.val (extChartAt Model p.val).symm z‖ ≤ C₀*M := by
  obtain ⟨C₀,hC,hbound⟩ := ddstar_scaled_basis_jet_bound J α hs ht p.val (D p) b L hK (hKU.trans hUD)
  refine ⟨C₀,hC,fun H Gs f z hz r M hr hr1 hj => ?_⟩
  rw [closedLiftOfInverse_pullback_sub]
  apply hbound (Gs f).val.val (Gs f).val.property (Gs f).property U hU hUD
    (localizedRawSchwartz A J α hs ht D hD p τ η (Gs f)) _ z (hKU hz) hz r M hr hr1 hj
  intro y hy
  exact (localizedRawSchwartz_raw A J α hs ht D hD p τ η (Gs f) (hUD hy)
    (hτ y hy) (hη y hy)).symm

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

theorem geometric_center_energy_two_jet (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (_hr : 0 < t.1),
      ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)) (M : ℝ), 0 ≤ M →
      (∀ z ∈ W, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
      (∀ k ≤ 3, ∀ v : Fin k → Space, (∀ i, ‖v i‖ ≤ 1) → ∀ x,
        ‖(∂^{v} (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
          (SchwartzMap.postcompCLM (embed 2) g))) x‖ ≤ M/t.1^k) →
      (∀ v : antiEnergy A J α hs ht,
        ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht a),weakDelta A J α hs ht v⟫ =
          ⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫) →
      let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm
        (localizedRawSchwartz A J α hs ht D hD p τ η a)
      ∀ x : Space, ((χ 4 : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1) →
        t.1*‖u (t.1 • x+L t.2)‖ + t.1^2*∑ i, ‖(∂_{stdOrthonormalBasis ℝ Space i} u) (t.1 • x+L t.2)‖ +
          t.1^3*∑ i, ∑ j, ‖(∂_{stdOrthonormalBasis ℝ Space j} (∂_{stdOrthonormalBasis ℝ Space i} u)) (t.1 • x+L t.2)‖ ≤
        C₀*(M*t.1^3 + ‖antiToEnergy A J α hs ht a‖) := by
  obtain ⟨d⟩ := exists_geometric_square_data A J α hs ht D p hU hUD q hq
  obtain ⟨η₀,hη₀,hηW,V,hV,hqV,hVW,hηone⟩ := SchwartzCutoff.exists_one_near d.openW d.qW
  let η := SchwartzMap.postcompCLM Complex.ofRealCLM η₀
  have hηs : tsupport η ⊆ tsupport η₀ := tsupport_comp_subset (map_zero Complex.ofRealCLM) η₀
  have hηc : HasCompactSupport (η : Space → ℂ) := hη₀.of_isClosed_subset (isClosed_tsupport η) hηs
  have hη (z) (hz : z ∈ V) : η z = 1 := by
    simp only [η,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hηone z hz,Complex.ofReal_one]
  obtain ⟨L,C₀,hC,hest⟩ := metric_square_center_energy_two_jet q (coordinateMetric J α ht p.val q)
    (fun i => (D p).frame i q) (fun i j => (D p).frame_gram q (hUD hq) i j)
    d.a d.b d.ρ d.g d.polarized (chartDensity J α p.val q)
    (chartDensity_pos J α ht p.val ((D p).domain_subset (hUD hq))) d.center ζ hζ χ hχ hζχ
  obtain ⟨K,hK,hcritical⟩ := raw_critical_norm A J α hs ht D hD p τ η hηc L
  have hshrink : ∀ᶠ t : ℝ × Space in 𝓝 (0,q), ∀ n : Fin 4, ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr (χ (n.val+1))) ⊆ V := by
    apply (Filter.eventually_all.mpr ?_)
    intro n
    exact normalizedCutoff_eventually_support L q (χ (n.val+1)) (hcχ n.val (by omega)) hV hqV
  refine ⟨d.W,V,d.openW,d.qW,d.WU,hV,hqV,hVW,η,hηc,hη,L,C₀*(K+1),by positivity,?_⟩
  filter_upwards [hest,hshrink] with t hh hsupport
  intro hr f a g M hM hg hderiv heq
  dsimp only
  have hPDE : ∀ n ≤ 3, smulLeftCLM (C 2) (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1)))
      (square EuclideanEnergy.e d.a d.b d.ρ (localizedRawSchwartz A J α hs ht D hD p τ η a : 𝓢'(Space,C 2))) =
      smulLeftCLM (C 2) (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1)))
        (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
    intro n hn
    have hv := hsupport ⟨n,by omega⟩ hr.ne'
    apply actual_localized_square_source A J α hs ht D hD p τ hUD hτ d η _
      (normalizedCutoff_compact L t.2 t.1 hr.ne' _ (hcχ n hn)) (hv.trans hVW) ?_ f a g hg heq
    intro z hz
    filter_upwards [hV.mem_nhds (hv hz)] with y hy
    exact hη y hy
  have hb := hh hr (localizedRawSchwartz A J α hs ht D hD p τ η a)
    (SchwartzMap.postcompCLM (embed 2) g) M hM hderiv hPDE
  intro x hx
  apply (hb x hx).trans
  have hk := hcritical a
  have hpow : 0 ≤ M*t.1^3 := mul_nonneg hM (pow_nonneg hr.le _)
  calc
    _ ≤ C₀*(M*t.1^3+K*‖antiToEnergy A J α hs ht a‖) :=
      mul_le_mul_of_nonneg_left (by linarith only [hk]) hC
    _ ≤ C₀*(K+1)*(M*t.1^3+‖antiToEnergy A J α hs ht a‖) := by
      nlinarith [norm_nonneg (antiToEnergy A J α hs ht a),mul_nonneg hK hpow]
end TamingCompatibility.GeometricHilbert

end
end

end
end
end

end OAI
