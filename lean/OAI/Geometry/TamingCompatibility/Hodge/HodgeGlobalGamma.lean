import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalCorrection
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGammaSplit

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldLocalization ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)

lemma globalGamma_bounds_of (n : ℕ) {T L C : ℝ}
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T))
    {r : ℝ} (hr : 0 < r) :
    let := geometricMetricSpace J α hs ht
    ∀ x y : X,
      (IntegrableOn (fun s : ℝ => hodgeGammaWeight s • globalLeading J α ht A E (r^2*s) x y)
        (Ioc 0 (T/r^2)) ∧
       VolterraBounds.weight n (r^2) x y *
        ‖HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r x y‖ ≤
          ((1/120:ℝ)*L*2^(n-1)*(HodgeKernelBounds.moment 3 1+HodgeKernelBounds.moment (3+n) 1))/r^4) ∧
      (IntegrableOn (fun s : ℝ => hodgeGammaWeight s • globalError J α ht A E T (r^2*s) x y)
        (Ioc 0 (T/r^2)) ∧
       VolterraBounds.weight n (r^2) x y *
        ‖HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r x y‖ ≤
          ((1/120:ℝ)*(4*L*C)*2^(n-1)*(HodgeKernelBounds.moment 4 1+HodgeKernelBounds.moment (4+n) 1))/r^2) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  have hEm := VolterraKernel.convolution_measurable (geometricVolume A J α) _ _
    hL.measurable hC.measurable
  intro x y
  constructor
  · exact HodgeKernelBounds.gammaKernel_bound 3 2 n (by norm_num) hr hL.nonneg _ x y
      ((hL.measurable.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,x,y)) by fun_prop)).aestronglyMeasurable)
      (fun t htp => hL.sup t htp x y)
  · apply HodgeKernelBounds.gammaKernel_bound 4 1 n (by norm_num) hr
      (by have := hL.nonneg; have := hC.nonneg; positivity) _ x y
      ((hEm.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,x,y)) by fun_prop)).aestronglyMeasurable)
    intro t htp
    simpa only [pow_one] using
      (VolterraKernel.convolution_sup (geometricVolume A J α) n _ _ hL hC htp x y).2

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open Set Filter MeasureTheory
variable {X B : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

omit [CompleteSpace B] in
lemma gammaKernel_continuous (q k : ℕ) (hqk : q+k=5) {T r A : ℝ} (hr : 0 < r)
    (K : ℝ → X → X → B)
    (hKm : StronglyMeasurable (fun p : ℝ × X × X => K p.1 p.2.1 p.2.2))
    (hK : ∀ t ∈ Ioc 0 T, ∀ x y, ‖K t x y‖ ≤ A/t^k)
    (hKc : ∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => K t p.1 p.2)) :
    Continuous (fun p : X × X => gammaKernel K T r p.1 p.2) := by
  let ν := volume.restrict (Ioc 0 (T/r^2))
  let G := fun (p : X × X) (s : ℝ) => hodgeGammaWeight s • K (r^2*s) p.1 p.2
  let m := fun s : ℝ => A/r^(2*k)*(Real.exp (-s)*s^q)
  have hm : Integrable m ν := by
    have h := polynomialMoment_integrable q 0
    simp only [pow_zero,mul_one] at h
    exact (h.mono_set (fun _ h => h.1)).const_mul _
  have hst (s : ℝ) (hs : s ∈ Ioc 0 (T/r^2)) : r^2*s ∈ Ioc 0 T :=
    ⟨mul_pos (sq_pos_of_pos hr) hs.1,by
      have h := (le_div_iff₀ (sq_pos_of_pos hr)).mp hs.2
      simpa only [mul_comm] using h⟩
  have hGm (p : X × X) : AEStronglyMeasurable (G p) ν :=
    hodgeGammaWeight_continuous.aestronglyMeasurable.smul
      ((hKm.comp_measurable (show Measurable (fun s : ℝ => (r^2*s,p.1,p.2)) by fun_prop)).aestronglyMeasurable)
  have hGb (p : X × X) : ∀ᵐ s ∂ν, ‖G p s‖ ≤ m s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hb : VolterraBounds.weight 0 (r^2*s) p.1 p.2 * ‖K (r^2*s) p.1 p.2‖ ≤ A/(r^2*s)^k := by
      simpa only [VolterraBounds.weight,pow_zero,one_mul] using hK _ (hst s hs) p.1 p.2
    simpa only [VolterraBounds.weight,pow_zero,one_mul,mul_one] using
      weighted_gamma_integrand q k 0 hqk hr hs.1 K p.1 p.2 hb
  have hGc : ∀ᵐ s ∂ν, Continuous (fun p => G p s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact continuous_const.smul (hKc _ (hst s hs))
  exact (continuous_of_dominated hGm hGb hm hGc).const_smul (1/120 : ℝ)

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldLocalization ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
omit [SecondCountableTopology X] [BorelSpace X] in
lemma globalLeading_gamma_continuous {T L r : ℝ} (hr : 0 < r)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E)) :
    Continuous (fun p : X × X => HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r p.1 p.2) := by
  let := geometricMetricSpace J α hs ht
  apply HodgeKernelBounds.gammaKernel_continuous 3 2 (by norm_num) hr _ hL.measurable
  · intro t htp x y
    simpa only [VolterraBounds.weight,pow_zero,one_mul] using hL.sup t htp x y
  · intro t htp
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (globalLeading_continuousAt A J α hs ht E hE htp.1 p.1 p.2).comp
      (continuous_const.prodMk continuous_id).continuousAt

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

lemma continuous_kernel_nonneg_of_smooth_tests (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (K : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      0 ≤ ∫ x, ∫ y, φ x*ψ y*K x y ∂μ ∂μ) :
    ∀ x y, 0 ≤ K x y := by
  intro x y
  by_contra hn
  have hneg : K x y < 0 := lt_of_not_ge hn
  have hnh : {p : X × X | K p.1 p.2 < 0} ∈ 𝓝 (x,y) :=
    (isOpen_lt hK continuous_const).mem_nhds hneg
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hnh
  obtain ⟨φ,_,hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) x).mem_iff.mp hU
  obtain ⟨ψ,_,hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) y).mem_iff.mp hV
  let F : X × X → ℝ := fun p => φ p.1*ψ p.2*K p.1 p.2
  have hFc : Continuous F := (φ.continuous.comp continuous_fst).mul
    (ψ.continuous.comp continuous_snd) |>.mul hK
  have hFi : Integrable F (μ.prod μ) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFneg : F ≤ 0 := by
    intro p
    by_cases hp : φ p.1 = 0
    · simp only [F,hp,zero_mul]; rfl
    by_cases hq : ψ p.2 = 0
    · simp only [F,hq,mul_zero,zero_mul]; rfl
    have hn := hUV ⟨hφ (subset_tsupport _ hp),hψ (subset_tsupport _ hq)⟩
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg φ.nonneg ψ.nonneg) hn.le
  have hzero : ∫ p, (-F p) ∂μ.prod μ = 0 := by
    have ht := htest φ ψ φ.contMDiff ψ.contMDiff (fun _ => φ.nonneg) (fun _ => ψ.nonneg)
    have hpos : 0 ≤ ∫ p, F p ∂μ.prod μ := by
      rw [integral_prod F hFi]
      exact ht
    rw [integral_neg]
    exact neg_eq_zero.mpr (le_antisymm (integral_nonpos hFneg) hpos)
  have hae : (fun p => -F p) =ᵐ[μ.prod μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => neg_nonneg.mpr (hFneg p)) hFi.neg).mp hzero
  have heq := Measure.eq_of_ae_eq hae hFc.neg continuous_const
  have hxy := congrFun heq (x,y)
  have hKzero : K x y = 0 := by
    simpa only [F,φ.eq_one,ψ.eq_one,one_mul,Pi.zero_apply,neg_eq_zero] using hxy
  exact hneg.ne hKzero

lemma continuous_kernel_le_of_smooth_tests (μ : Measure X) [IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (K L : X → X → ℝ)
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hL : Continuous (fun p : X × X => L p.1 p.2))
    (htest : ∀ φ ψ : X → ℝ, ContMDiff Model 𝓘(ℝ,ℝ) ∞ φ →
      ContMDiff Model 𝓘(ℝ,ℝ) ∞ ψ → (∀ x, 0 ≤ φ x) → (∀ y, 0 ≤ ψ y) →
      (∫ x, ∫ y, φ x*ψ y*K x y ∂μ ∂μ) ≤ ∫ x, ∫ y, φ x*ψ y*L x y ∂μ ∂μ) :
    ∀ x y, K x y ≤ L x y := by
  have hn := continuous_kernel_nonneg_of_smooth_tests μ (fun x y => L x y-K x y)
    (hL.sub hK) ?_
  · intro x y
    exact sub_nonneg.mp (hn x y)
  intro φ ψ hφ hψ hp hq
  have hFi (Z : X → X → ℝ) (hZ : Continuous (fun p : X × X => Z p.1 p.2)) :
      Integrable (fun p : X × X => φ p.1*ψ p.2*Z p.1 p.2) (μ.prod μ) :=
    (((hφ.continuous.comp continuous_fst).mul (hψ.continuous.comp continuous_snd)).mul hZ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_prod _ (hFi (fun x y => L x y-K x y) (hL.sub hK))]
  simp_rw [mul_sub]
  rw [integral_sub (hFi L hL) (hFi K hK),integral_prod _ (hFi L hL),integral_prod _ (hFi K hK)]
  exact sub_nonneg.mpr (htest φ ψ hφ hψ hp hq)

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
