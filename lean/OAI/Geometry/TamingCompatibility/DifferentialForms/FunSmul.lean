import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.CoordinateIntegrand
import OAI.Geometry.TamingCompatibility.DifferentialForms.Sign

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] {k : ℕ}

omit [IsManifold Model ∞ X] in
lemma Smooth.fun_smul {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    {β : Form X k} (hβ : Smooth β) : Smooth (fun x => f x • β x) := by
  intro g U hU hg
  change ContDiffOn ℝ ∞ (fun z => f (g z) • pullback β g z) U
  exact (hf.comp_contMDiffOn hg).contDiffOn.smul (hβ g U hU hg)

omit [IsManifold Model ∞ X] in
lemma exteriorDerivative_eq_zero_of_eventually (β : Form X k) (x : X)
    (hβ : ∀ᶠ y in 𝓝 x, β y = 0) : exteriorDerivative β x = 0 := by
  have h : pullback β (extChartAt Model x).symm =ᶠ[𝓝 ((extChartAt Model x) x)]
      (fun _ => (0 : Space [⋀^Fin k]→L[ℝ] ℝ)) := by
    have hc := continuousAt_extChartAt_symm (I := Model) x
    have hβ' : ∀ᶠ y in 𝓝 ((extChartAt Model x).symm ((extChartAt Model x) x)), β y = 0 := by
      rwa [(extChartAt Model x).left_inv (mem_extChartAt_source x)]
    filter_upwards [hc.eventually hβ'] with z hz
    simp only [pullback,hz]
    ext v
    rfl
  change extDeriv (pullback β (extChartAt Model x).symm) ((extChartAt Model x) x) = 0
  rw [h.extDeriv_eq]
  simp [extDeriv,← alternatizeUncurryFinCLM_apply]

omit [IsManifold Model ∞ X] in
lemma exteriorDerivative_fun_smul_vanishes {f : X → ℝ} (β : Form X k) {x : X}
    (hx : x ∉ tsupport f) : exteriorDerivative (fun y => f y • β y) x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]

end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.EuclideanStokes
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_directional_eq_zero {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (v : E) : (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have hc' : HasCompactSupport (fun x => fderiv ℝ f x v) := by
    exact hc.fderiv_apply (𝕜 := ℝ) v
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := μ) (f := fun _ : E => (1 : ℝ)) (f' := fun _ => (0 : ℝ))
    (g := f) (g' := fun x => fderiv ℝ f x v) (v := v)
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simp only [ContinuousLinearMap.mul_apply',zero_mul]; exact integrable_zero _ _ _)
    (by simpa using hd.continuous.integrable_of_hasCompactSupport hc')
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => ((hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).hasLineDerivAt v))
    (fun x _ => (hf.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v)
  simpa using hi

lemma integral_extDeriv_eq_zero {k : ℕ} {α : E → E [⋀^Fin k]→L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hc : HasCompactSupport α) (v : Fin (k+1) → E) :
    (∫ x, extDeriv α x v ∂μ) = 0 := by
  have hs (i : Fin (k+1)) : ContDiff ℝ ∞ (fun x => α x (i.removeNth v)) :=
    (ContinuousAlternatingMap.apply ℝ E ℝ (i.removeNth v)).contDiff.comp hα
  have hk (i : Fin (k+1)) : HasCompactSupport (fun x => α x (i.removeNth v)) :=
    hc.comp_left (g := fun a : E [⋀^Fin k]→L[ℝ] ℝ => a (i.removeNth v)) rfl
  have he : (fun x => extDeriv α x v) =
      (fun x => ∑ i : Fin (k+1), (-1 : ℝ) ^ i.val * fderiv ℝ (fun y => α y (i.removeNth v)) x (v i)) := by
    ext x
    simpa only [smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using extDeriv_apply (hα.differentiable (by simp) x) v
  rw [he,integral_finsetSum]
  · simp_rw [integral_const_mul,integral_directional_eq_zero (μ := μ) (hs _) (hk _),mul_zero]
    simp
  · intro i _
    apply Integrable.const_mul
    have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => α y (i.removeNth v)) x (v i)) :=
      ((hs i).fderiv_right (by simp)).clm_apply contDiff_const
    exact hd.continuous.integrable_of_hasCompactSupport
      ((hk i).fderiv_apply (𝕜 := ℝ) (v i))
end TamingCompatibility.EuclideanStokes

namespace TamingCompatibility.SignedStokes
open MeasureTheory Set ContinuousAlternatingMap
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_extDeriv_on_open {k : ℕ} {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {ν : E → ℝ}
    (hν : ContDiffOn ℝ ∞ ν U) (hn : ∀ x ∈ U, ν x ≠ 0)
    {β : E → E [⋀^Fin k]→L[ℝ] ℝ} (hβ : ContDiffOn ℝ ∞ β U)
    (hz : ∀ x ∈ U, x ∉ K → β x = 0) (v : Fin (k+1) → E) :
    (∫ x in U, OrientationSign.sign (ν x) * extDeriv β x v ∂μ) = 0 := by
  let G : E → E [⋀^Fin k]→L[ℝ] ℝ := U.indicator (fun x => OrientationSign.sign (ν x) • β x)
  have hGz (x : E) (hx : x ∉ K) : G x = 0 := by
    by_cases hxU : x ∈ U
    · rw [show G x = OrientationSign.sign (ν x) • β x from indicator_of_mem hxU _,hz x hxU hx,smul_zero]
    · exact indicator_of_notMem hxU _
  have hG := ManifoldLocalization.smooth_indicator_of_compact hU hK hKU
    ((OrientationSign.contDiffOn hU hν.continuousOn hn).smul hβ)
    (fun x hx hxK => by change OrientationSign.sign (ν x) • β x = 0; rw [hz x hx hxK,smul_zero])
  have he (x : E) : extDeriv G x = U.indicator
      (fun y => OrientationSign.sign (ν y) • extDeriv β y) x := by
    by_cases hx : x ∈ U
    · have hg : G =ᶠ[𝓝 x] (fun y => OrientationSign.sign (ν y) • β y) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact indicator_of_mem hy _
      rw [hg.extDeriv_eq,OrientationSign.extDeriv_smul hU hν.continuousOn hx (hn x hx),indicator_of_mem hx]
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have hg : G =ᶠ[𝓝 x] (fun _ => (0 : E [⋀^Fin k]→L[ℝ] ℝ)) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
        exact hGz y hy
      rw [hg.extDeriv_eq,indicator_of_notMem hx]
      simp [extDeriv,← alternatizeUncurryFinCLM_apply]
  rw [← integral_indicator hU.measurableSet]
  have hev : U.indicator (fun x => OrientationSign.sign (ν x) * extDeriv β x v) =
      fun x => extDeriv G x v := by
    funext x
    rw [he]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx,indicator_of_mem hx]
      rfl
    · simp only [indicator_of_notMem hx,ContinuousAlternatingMap.coe_zero,Pi.zero_apply]
  rw [hev]
  exact EuclideanStokes.integral_extDeriv_eq_zero hG.1 hG.2 v

end TamingCompatibility.SignedStokes

namespace TamingCompatibility.ManifoldStokes
open Bundle ContinuousAlternatingMap MeasureTheory Set
open ManifoldForms ManifoldTop ManifoldVolume
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coefficient_add (J : AlmostComplexStructure X) (α : TwoForm X)
    (β γ : ManifoldForms.Form X 4) :
    ManifoldTop.coefficient J α (β + γ) = ManifoldTop.coefficient J α β + ManifoldTop.coefficient J α γ := by
  funext x
  change ((β x) basis + (γ x) basis) / volumeForm J α x basis = _
  exact add_div _ _ _

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coefficient_smul (J : AlmostComplexStructure X) (α : TwoForm X)
    (β : ManifoldForms.Form X 4) (c : ℝ) :
    ManifoldTop.coefficient J α (c • β) = c • ManifoldTop.coefficient J α β := by
  funext x
  change (c * β x basis) / volumeForm J α x basis = c * (β x basis / volumeForm J α x basis)
  exact mul_div_assoc _ _ _

omit [T2Space X] in
lemma coefficient_integrable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) {β : ManifoldForms.Form X 4} (hβ : Smooth β) :
    Integrable (ManifoldTop.coefficient J α β) (geometricVolume A J α) := by
  let _ := geometricVolume_finite A J α hs ht
  exact (coefficient_smooth J α hs ht hβ).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

def integral (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    smoothForms X 4 →ₗ[ℝ] ℝ where
  toFun β := ∫ x, ManifoldTop.coefficient J α β.1 x ∂geometricVolume A J α
  map_add' β γ := by
    change (∫ x, ManifoldTop.coefficient J α (β.1 + γ.1) x ∂geometricVolume A J α) = _
    rw [coefficient_add]
    exact integral_add (coefficient_integrable A J α hs ht β.2) (coefficient_integrable A J α hs ht γ.2)
  map_smul' c β := by
    change (∫ x, ManifoldTop.coefficient J α (c • β.1) x ∂geometricVolume A J α) = _
    rw [coefficient_smul]
    exact integral_smul c _

omit [T2Space X] in
lemma integral_exteriorDerivative_cutoff (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) (f : X → ℝ)
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (hfp : tsupport f ⊆ (extChartAt Model p).source)
    (β : ManifoldForms.Form X 3) (hβ : Smooth β) :
    integral A J α hs ht ⟨exteriorDerivative (fun x => f x • β x),(hβ.fun_smul hf).exteriorDerivative⟩ = 0 := by
  let γ : ManifoldForms.Form X 3 := fun x => f x • β x
  have hγ : Smooth γ := hβ.fun_smul hf
  have hcoeff : tsupport (ManifoldTop.coefficient J α (exteriorDerivative γ)) ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra h
    apply hx
    change (exteriorDerivative γ x basis) / volumeForm J α x basis = 0
    rw [show exteriorDerivative γ x = 0 from exteriorDerivative_fun_smul_vanishes β h]
    change (0 : ℝ) / _ = 0
    exact zero_div _
  change (∫ x, ManifoldTop.coefficient J α (exteriorDerivative γ) x ∂geometricVolume A J α) = 0
  rw [integral_geometricVolume_coordinate A J α hs ht p _
    (coefficient_smooth J α hs ht hγ.exteriorDerivative).continuous (hcoeff.trans hfp)]
  let ν : Space → ℝ := fun z => ManifoldForms.pullback (volumeForm J α) (extChartAt Model p).symm z basis
  have hν : ContDiffOn ℝ ∞ ν (extChartAt Model p).target :=
    (ContinuousAlternatingMap.apply ℝ Space ℝ basis).contDiff.comp_contDiffOn
      (smooth_chart _ (volumeForm_smooth J α hs) p)
  let K : Set Space := (extChartAt Model p) '' tsupport f
  have hK : IsCompact K := (isClosed_tsupport f).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt p).mono hfp)
  have hKU : K ⊆ (extChartAt Model p).target := by
    rintro z ⟨x,hx,rfl⟩
    exact (extChartAt Model p).map_source (hfp hx)
  calc
    _ = ∫ z in (extChartAt Model p).target, OrientationSign.sign (ν z) *
        extDeriv (ManifoldForms.pullback γ (extChartAt Model p).symm) z basis := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target p).measurableSet
      intro z hz
      dsimp only
      rw [density_coefficient J α ht (exteriorDerivative γ) p hz]
      rw [pullback_exteriorDerivative γ hγ (isOpen_extChartAt_target p)
        (contMDiffOn_extChartAt_symm p) hz,extDerivWithin_eq_of_mem (isOpen_extChartAt_target p) hz]
    _ = 0 := by
      apply SignedStokes.integral_extDeriv_on_open (isOpen_extChartAt_target p) hK hKU hν
        (fun z hz => coordinateVolume_ne_zero J α ht p hz) (smooth_chart γ hγ p)
      intro z hz hnK
      have hn : (extChartAt Model p).symm z ∉ tsupport f := by
        intro h
        exact hnK ⟨(extChartAt Model p).symm z,h,(extChartAt Model p).right_inv hz⟩
      change ((f ((extChartAt Model p).symm z) • β ((extChartAt Model p).symm z)).compContinuousLinearMap _) = 0
      rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
      ext v
      rfl

omit [T2Space X] in

theorem stokes (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (β : smoothForms X 3) : integral A J α hs ht (d β) = 0 := by
  classical
  let βp (p : A.centers) : smoothForms X 3 :=
    ⟨fun x => A.partition p x • β.1 x,β.2.fun_smul (A.partition p).contMDiff⟩
  have hsum : ∑ p : A.centers, βp p = β := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ p : A.centers, A.partition p x • β.1 x) = β.1 x
    rw [← Finset.sum_smul,ManifoldLocalization.partition_sum,one_smul]
  rw [← hsum,_root_.map_sum,_root_.map_sum]
  apply Finset.sum_eq_zero
  intro p _
  exact integral_exteriorDerivative_cutoff A J α hs ht p.val (A.partition p)
    (A.partition p).contMDiff (A.subordinate p) β.1 β.2

end TamingCompatibility.ManifoldStokes

end

end OAI
