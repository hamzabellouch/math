import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RawCriticalNorm
import OAI.Geometry.TamingCompatibility.DifferentialForms.LinearCenterEnergy
import OAI.Geometry.TamingCompatibility.Functional.GeometricLocalPDE

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open Set Filter
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalizedCutoff (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
    (affineSchwartz (-(r⁻¹ • L q)) r⁻¹ (inv_ne_zero hr) χ)

lemma normalizedCutoff_apply (L : E ≃L[ℝ] E) (q y : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : normalizedCutoff L q r hr χ y = χ (r⁻¹ • L y - r⁻¹ • L q) := by
  rw [normalizedCutoff,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    affineSchwartz_apply,sub_eq_add_neg]

lemma normalizedCutoff_support (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) : tsupport (normalizedCutoff L q r hr χ) ⊆
      (fun y => r⁻¹ • L y - r⁻¹ • L q) ⁻¹' tsupport χ := by
  apply closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
  intro y hy
  apply subset_tsupport χ
  simpa only [Function.mem_support,normalizedCutoff_apply] using hy

lemma normalizedCutoff_compact (L : E ≃L[ℝ] E) (q : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) (hc : HasCompactSupport (χ : E → ℂ)) :
    HasCompactSupport (normalizedCutoff L q r hr χ : E → ℂ) := by
  have hk := hc.image (show Continuous (fun z => r • L.symm z+q) by fun_prop)
  apply hk.of_isClosed_subset (isClosed_tsupport _)
  intro y hy
  let z := r⁻¹ • L y-r⁻¹ • L q
  refine ⟨z,normalizedCutoff_support L q r hr χ hy,?_⟩
  apply L.injective
  simp only [map_add,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
    smul_sub,smul_smul,mul_inv_cancel₀ hr,one_smul,sub_add_cancel]

lemma normalizedCutoff_eventually_support (L : E ≃L[ℝ] E) (q₀ : E)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    {W : Set E} (hW : IsOpen W) (hq : q₀ ∈ W) :
    ∀ᶠ t : ℝ × E in 𝓝 (0,q₀), ∀ hr : t.1 ≠ 0,
      tsupport (normalizedCutoff L t.2 t.1 hr χ) ⊆ W := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hW q₀ hq
  obtain ⟨R,hR⟩ := hχ.exists_bound_of_continuousOn (f := fun x : E => x) continuous_id.continuousOn
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  have hc : Continuous (fun t : ℝ × E => ‖t.2-q₀‖+|t.1| *‖(L.symm : E →L[ℝ] E)‖*B) := by fun_prop
  have ht : ∀ᶠ t : ℝ × E in 𝓝 (0,q₀), ‖t.2-q₀‖+|t.1| *‖(L.symm : E →L[ℝ] E)‖*B < δ :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa using hδ)
  filter_upwards [ht] with t ht
  intro hr y hy
  let z := t.1⁻¹ • L y - t.1⁻¹ • L t.2
  have hz : z ∈ tsupport χ := normalizedCutoff_support L t.2 t.1 hr χ hy
  have hze : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
  have he : y-t.2 = t.1 • L.symm z := by
    apply L.injective
    simp only [map_sub,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
      smul_sub,smul_smul,mul_inv_cancel₀ hr,one_smul]
  have hnorm : ‖y-t.2‖ ≤ |t.1| *‖(L.symm : E →L[ℝ] E)‖*B := by
    rw [he,norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left ((L.symm : E →L[ℝ] E).le_opNorm z) (abs_nonneg _)).trans
    calc
      _ ≤ |t.1| *(‖(L.symm : E →L[ℝ] E)‖*B) := by gcongr
      _ = _ := by ring
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  calc
    ‖y-q₀‖ = ‖(y-t.2)+(t.2-q₀)‖ := by congr 1; abel
    _ ≤ ‖y-t.2‖+‖t.2-q₀‖ := norm_add_le _ _
    _ ≤ |t.1| *‖(L.symm : E →L[ℝ] E)‖*B+‖t.2-q₀‖ := add_le_add hnorm le_rfl
    _ < δ := by linarith
end TamingCompatibility.EuclideanSobolevOperators

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

theorem geometric_center_local_energy_two_jet (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U)
    (ζ : 𝓢(Space,ℂ)) (hζ : HasCompactSupport (ζ : Space → ℂ))
    (χ : ℕ → 𝓢(Space,ℂ)) (hcχ : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ))
    (hχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1)
    (hζχ : ∀ n ≤ 3, ∀ x ∈ tsupport (χ (n+1)), ζ x = 1) :
    ∃ W V : Set Space, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      ∃ η : 𝓢(Space,ℂ), HasCompactSupport (η : Space → ℂ) ∧ (∀ x ∈ V, η x = 1) ∧
      ∃ L : Space ≃L[ℝ] Space, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ t in 𝓝 (0,q), ∀ (hr : 0 < t.1),
      ∀ (f a : antiPre A J α hs ht) (g : 𝓢(Space,EuclideanEnergy.Pair)) (M : ℝ), 0 ≤ M →
      (∃ O : Set Space, IsOpen O ∧ O ⊆ W ∧
        (∀ n ≤ 3, tsupport (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1))) ⊆ O) ∧
        ∀ z ∈ O, g z = (2*chartDensity J α p.val z) • rawPair J α ht p.val (D p) f.val.val z) →
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
  obtain ⟨O,hO,hOW,hχO,hg⟩ := hg
  dsimp only
  have hPDE : ∀ n ≤ 3, smulLeftCLM (C 2) (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1)))
      (square EuclideanEnergy.e d.a d.b d.ρ (localizedRawSchwartz A J α hs ht D hD p τ η a : 𝓢'(Space,C 2))) =
      smulLeftCLM (C 2) (normalizedCutoff L t.2 t.1 hr.ne' (χ (n+1)))
        (SchwartzMap.postcompCLM (embed 2) g : 𝓢'(Space,C 2)) := by
    intro n hn
    have hv := hsupport ⟨n,by omega⟩ hr.ne'
    apply actual_localized_square_source_on A J α hs ht D hD p τ hUD hτ d hO hOW η _
      (normalizedCutoff_compact L t.2 t.1 hr.ne' _ (hcχ n hn)) (hχO n hn) ?_ f a g hg heq
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
