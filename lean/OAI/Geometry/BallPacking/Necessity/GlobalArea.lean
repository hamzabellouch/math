import Mathlib
import OAI.Geometry.BallPacking.Rigidity.CorrectedInfinity

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

theorem outerProfile_one {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t ≤ A) :
    outerProfile A t = 1 := by
  simp only [outerProfile,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + 2),
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htA) hA.le),
    sub_zero, mul_one]

theorem outerProfile_le_one (A t : ℝ) : outerProfile A t ≤ 1 := by
  unfold outerProfile
  calc
    _ ≤ 1 * (1 - Real.smoothTransition ((t-A)/A)) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (sub_nonneg.mpr (Real.smoothTransition.le_one _))
    _ ≤ 1 := by linarith [Real.smoothTransition.nonneg ((t-A)/A)]

theorem outerProfile_mono {A B t : ℝ} (hA : 0 < A) (hAB : A ≤ B) (ht : 0 ≤ t) :
    outerProfile A t ≤ outerProfile B t := by
  have hB : 0 < B := hA.trans_le hAB
  have hd : (t-B)/B ≤ (t-A)/A := by
    rw [div_le_div_iff₀ hB hA]
    nlinarith
  unfold outerProfile
  apply mul_le_mul_of_nonneg_left _ (Real.smoothTransition.nonneg _)
  exact sub_le_sub_left (Real.smoothTransition.monotone hd) 1

 
def cutoffCurl (β : Plane → Plane →L[ℝ] ℝ) (A : ℝ) (z : Plane) : ℝ :=
  outerProfile A (radiusSq z) * planarCurl β z

theorem cutoffCurl_integrable {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A : ℝ} (hA : 0 < A) : Integrable (cutoffCurl β A) := by
  exact (((outerProfile_smooth A).comp radiusSq_smooth).mul
    (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)).mul_right

theorem cutoffCurl_stokes {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A : ℝ} (hA : 0 < A) :
    (∫ z, cutoffCurl β A z) =
      - ∫ z : Plane, 2 * deriv (outerProfile A) (radiusSq z) * β z (planeRotation z) := by
  have he := integral_cutoffWedge ((outerProfile_smooth A).comp radiusSq_smooth)
    (HasCompactSupport.comp_radiusSq (outerProfile_compact hA)) hβ
  dsimp only [Function.comp_def] at he
  simp_rw [cutoffWedge_radial_rotation (outerProfile_smooth A)] at he
  change _ = - ∫ z, cutoffCurl β A z at he
  linarith

theorem cutoffCurl_bounds {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A k ε : ℝ} (hA : 0 < A)
    (he : ∀ z : Plane, A ≤ radiusSq z → |β z (planeRotation z) - k| ≤ ε) :
    2 * Real.pi * (k-ε) ≤ (∫ z, cutoffCurl β A z) ∧
      (∫ z, cutoffCurl β A z) ≤ 2 * Real.pi * (k+ε) := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hdi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z)) :=
    (((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2
  have hwi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z) * β z (planeRotation z)) := by
    have hh := cutoffWedge_integrable (hg.comp radiusSq_smooth)
      (HasCompactSupport.comp_radiusSq hgc) hβ
    dsimp only [Function.comp_def] at hh
    convert hh using 1
    ext z
    exact (cutoffWedge_radial_rotation hg (β := β) z).symm
  have hp (z : Plane) :
      2 * deriv g (radiusSq z) * (k+ε) ≤ 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧
      2 * deriv g (radiusSq z) * β z (planeRotation z) ≤ 2 * deriv g (radiusSq z) * (k-ε) := by
    by_cases hd : deriv g (radiusSq z) = 0
    · simp only [hd, mul_zero, zero_mul, le_refl, and_self]
    have hz : A ≤ radiusSq z := by
      by_contra! hn
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hn)
    have hb := abs_le.mp (he z hz)
    have hdn : 2 * deriv g (radiusSq z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num)
        (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (by linarith [hb.2]) hdn,
      mul_le_mul_of_nonpos_left (by linarith [hb.1]) hdn⟩
  have hlo := integral_mono (hdi.mul_const (k+ε)) hwi (fun z => (hp z).1)
  have hhi := integral_mono hwi (hdi.mul_const (k-ε)) (fun z => (hp z).2)
  have hg0 : g 0 = 1 := outerProfile_zero_value hA
  rw [integral_mul_const, integral_radial_derivative hg hgc, hg0] at hlo hhi
  rw [cutoffCurl_stokes hβ hA]
  change _ ≤ - ∫ z : Plane, 2 * deriv g (radiusSq z) * β z (planeRotation z) ∧ _
  constructor <;> nlinarith

theorem tendsto_integral_cutoffCurl {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => ∫ z, cutoffCurl β A z) atTop (𝓝 (2 * Real.pi * k)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (4 * Real.pi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : 2 * Real.pi * δ = ε / 2 := by
    dsimp [δ]
    field_simp
    ring
  have he : ∀ᶠ z in cocompact Plane, |β z (planeRotation z) - k| ≤ δ := by
    filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ] with z hz
    exact (Real.dist_eq _ _ ▸ hz).le
  obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
  obtain ⟨B,hB,hbound⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  filter_upwards [eventually_ge_atTop (B+1)] with A hA
  have hApos : 0 < A := by linarith
  have hb := cutoffCurl_bounds hβ hApos (k := k) (ε := δ) (by
    intro z hz
    apply hKs
    intro hzK
    have hx := hbound (radiusSq z) ⟨z,hzK,rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (radiusSq_nonneg z)] at hx
    linarith)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> nlinarith [hb.1, hb.2]

 

theorem integral_planarCurl_of_nonneg_of_angular_limit
    {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β)
    (hpos : ∀ z, 0 ≤ planarCurl β z) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Integrable (planarCurl β) ∧ (∫ z, planarCurl β z) = 2 * Real.pi * k := by
  have hA (j : ℕ) : 0 < (j : ℝ) + 1 := by positivity
  have hcpos (A : ℝ) (z : Plane) : 0 ≤ cutoffCurl β A z :=
    mul_nonneg (outerProfile_nonneg _ _) (hpos z)
  have hnlim : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hcutlim := (tendsto_integral_cutoffCurl hβ hlim).comp hnlim
  have hknonneg : 0 ≤ 2 * Real.pi * k :=
    ge_of_tendsto hcutlim (Filter.Eventually.of_forall fun j => integral_nonneg (hcpos _))
  have hmeas (j : ℕ) : AEMeasurable (fun z => ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) :=
    (ENNReal.continuous_ofReal.comp
      ((((outerProfile_smooth _).comp radiusSq_smooth).mul
        (planarCurl_contDiff hβ)).continuous)).aemeasurable
  have hmono : ∀ᵐ z : Plane, Monotone (fun j : ℕ => ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) := by
    apply Filter.Eventually.of_forall
    intro z i j hij
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (outerProfile_mono (hA i) (by exact_mod_cast Nat.add_le_add_right hij 1)
        (radiusSq_nonneg z)) (hpos z)
  have hpoint : ∀ᵐ z : Plane, Tendsto
      (fun j : ℕ => ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) atTop
      (𝓝 (ENNReal.ofReal (planarCurl β z))) := by
    apply Filter.Eventually.of_forall
    intro z
    apply Filter.EventuallyEq.tendsto
    filter_upwards [hnlim.eventually (eventually_ge_atTop (radiusSq z))] with j hj
    simp only [cutoffCurl, outerProfile_one (hA j) (radiusSq_nonneg z) hj, one_mul]
  have hm := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hpoint
  have heq (j : ℕ) : (∫⁻ z, ENNReal.ofReal (cutoffCurl β ((j:ℝ)+1) z)) =
      ENNReal.ofReal (∫ z, cutoffCurl β ((j:ℝ)+1) z) :=
    (ofReal_integral_eq_lintegral_ofReal (cutoffCurl_integrable hβ (hA j))
      (Filter.Eventually.of_forall (hcpos _))).symm
  simp_rw [heq] at hm
  have hmval := tendsto_nhds_unique hm (ENNReal.tendsto_ofReal hcutlim)
  have hi : Integrable (planarCurl β) := by
    refine ⟨(planarCurl_contDiff hβ).continuous.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _)]
    rw [hmval]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
    hi.aestronglyMeasurable, hmval, ENNReal.toReal_ofReal hknonneg]

 

theorem AffineLineCurve.total_radial_area {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x - standardJ n))
    {S T : ℝ} (hST : S < T) (hT : T < 1)
    (houtside : ∀ x, S < capacity x → J x = standardJ n) :
    Integrable (curveDensity S T u) ∧ (∫ z, curveDensity S T u z) = 1 := by
  have hcureq : planarCurl (curvePrimitive S T u) = curveDensity S T u :=
    funext (curvePrimitive_curl hST hu.1)
  have hh := integral_planarCurl_of_nonneg_of_angular_limit
    (curvePrimitive_smooth hST hu.1)
    (by simpa only [hcureq] using curveDensity_nonneg hST hT hJ houtside hu.2.1)
    (hu.radial_infinity_limit hc hST)
  rw [hcureq] at hh
  convert hh using 1
  field_simp

 

theorem affine_primitive_angular_limit_zero {n : ℕ} {u v : ℂ → Phase n}
    (hv : ContDiffAt ℝ ∞ v 0)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => v z⁻¹)
    {α : Phase n → Phase n →L[ℝ] ℝ} (hα : Continuous α) :
    Tendsto (fun z : ℂ => α (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hdu := (hv.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hdv : Tendsto (fun z : ℂ => fderiv ℝ v z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdu.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => α (v z⁻¹)) (cocompact ℂ) (𝓝 (α (v 0))) :=
    hα.continuousAt.tendsto.comp (hv.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => α (v z⁻¹) (fderiv ℝ v z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def, map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hprim.prodMk_nhds hdv)
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => v y⁻¹ := by
    obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
    filter_upwards [hK.compl_mem_cocompact] with z hz
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hKs hy
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ v w :=
    ((hv.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hw => hw.differentiableAt (by simp))
  apply hl.congr'
  filter_upwards [hnear, hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hvz hz0
  rw [hz.self_of_nhds, hz.fderiv_eq]
  have hiD : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz0).differentiableAt.restrictScalars ℝ
  have hh : HasFDerivAt (fun y : ℂ => v y⁻¹)
      ((fderiv ℝ v z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hvz.hasFDerivAt.comp z hiD.hasFDerivAt
  rw [hh.fderiv]
  change _ = α (v z⁻¹) (fderiv ℝ v z⁻¹ (fderiv ℝ (fun w : ℂ => w⁻¹) z (Complex.I*z)))
  rw [complex_inv_fderiv_real hz0]
  have heq : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [heq]

 

theorem affine_sphere_constant {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {S T : ℝ} (hST : S < T) (hT : T < 1)
    (houtside : ∀ x, S < capacity x → J x = standardJ n)
    {u v : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (huh : ∀ z, PseudoHolomorphicAt J u z)
    (hv : ContDiffAt ℝ ∞ v 0)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => v z⁻¹) :
    ∀ z, u z = u 0 := by
  have hlim : Tendsto (fun z : Plane => curvePrimitive S T u z (planeRotation z))
      (cocompact Plane) (𝓝 0) := by
    have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
      Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hh := (affine_primitive_angular_limit_zero hv he
      (radialPrimitiveCLM_smooth hST).continuous).comp hr
    apply hh.congr
    intro z
    change radialPrimitiveCLM S T _ _ = radialPrimitiveCLM S T _ _
    have hd := realCurve_fderiv (z := z) (hu.differentiable (by simp) _) (planeRotation z)
    rw [equivRealProd_rotation] at hd
    exact congrArg (radialPrimitiveCLM S T (u (Complex.equivRealProdCLM.symm z))) hd.symm
  have hcureq : planarCurl (curvePrimitive S T u) = curveDensity S T u :=
    funext (curvePrimitive_curl hST hu)
  have hpos := curveDensity_nonneg hST hT hJ houtside huh
  have hh := integral_planarCurl_of_nonneg_of_angular_limit
    (curvePrimitive_smooth hST hu) (by simpa only [hcureq] using hpos) hlim
  rw [hcureq, mul_zero] at hh
  have hden0 : curveDensity S T u = 0 :=
    ((curveDensity_smooth hST hu).continuous.ae_eq_iff_eq volume continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg hpos hh.1).mp hh.2)
  have hd1 (z : Plane) : fderiv ℝ (realCurve u) z (1,0) = 0 := by
    by_contra hn
    have hp := radialForm_adapted_pos hST hT hJ houtside (realCurve u z) hn
    have hz : curveDensity S T u z = 0 := congrFun hden0 z
    unfold curveDensity at hz
    rw [realCurve_CR (huh _)] at hz
    linarith
  have hd (z : Plane) : fderiv ℝ (realCurve u) z = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : w = w.1 • ((1,0) : Plane) + w.2 • ((0,1) : Plane) := by ext <;> simp
    rw [hw, map_add, map_smul, map_smul, hd1, realCurve_CR (huh _), hd1, map_zero]
    simp
  intro z
  have hh := is_const_of_fderiv_eq_zero ((realCurve_smooth hu).differentiable (by simp))
    hd (Complex.equivRealProdCLM z) 0
  simpa only [realCurve, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, map_zero] using hh

 

theorem exists_common_radial_interval {n : ℕ} {J : Phase n → End n}
    (hc : HasCompactSupport (fun x => J x - standardJ n))
    (hs : tsupport (fun x => J x - standardJ n) ⊆ openBall n 1) :
    ∃ S T : ℝ, 0 ≤ S ∧ S < T ∧ T < 1 ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S < capacity x →
        lineHomotopy J t x = standardJ n := by
  let K := insert (0 : Phase n) (tsupport (fun x => J x - standardJ n))
  have hK : IsCompact K := hc.insert 0
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn (by exact ⟨0,mem_insert _ _⟩)
    (capacity_smooth n).continuous.continuousOn
  have hS0 : 0 ≤ capacity x := by
    convert hmax (mem_insert (0 : Phase n) _) using 1
    simp [capacity]
  have hS1 : capacity x < 1 := by
    rcases hx with rfl | hx
    · simp [capacity]
    · exact hs hx
  refine ⟨capacity x,(capacity x+1)/2,hS0,by linarith,by linarith,?_⟩
  intro t ht y hy
  apply sub_eq_zero.mp
  apply image_eq_zero_of_notMem_tsupport (f := fun x => lineHomotopy J t x - standardJ n)
  intro hm
  exact (not_le_of_gt hy) (hmax (mem_insert_of_mem _ (lineHomotopy_support J ht hm)))

 

theorem homotopy_lines_have_common_unit_area {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x - standardJ n))
    (hs : tsupport (fun x => J x - standardJ n) ⊆ openBall n 1) :
    ∃ S T : ℝ, 0 ≤ S ∧ S < T ∧ T < 1 ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ p q : Phase n, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      Integrable (curveDensity S T u) ∧ (∫ z, curveDensity S T u z) = 1 := by
  obtain ⟨S,T,hS,hST,hT,hout⟩ := exists_common_radial_interval hc hs
  refine ⟨S,T,hS,hST,hT,?_⟩
  intro t ht p q u hu
  exact hu.total_radial_area (lineHomotopy_compatible hJ ht)
    (lineHomotopy_compact hc ht) hST hT (hout t ht)

 

theorem normalizedPrimitive_pole_infinity_curve {n : ℕ} {h : ℂ → Phase n}
    {z : ℂ} (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹)
    (hh0 : h z⁻¹ ≠ 0) (m : ℕ) :
    normalizedPrimitive (z^m • h z⁻¹)
      (fderiv ℝ (fun y : ℂ => y^m • h y⁻¹) z (Complex.I*z)) =
      (m:ℝ) / (2 * Real.pi) +
        normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)) := by
  have hi : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz).differentiableAt.restrictScalars ℝ
  have hg : DifferentiableAt ℝ (fun y : ℂ => h y⁻¹) z := hh.comp z hi
  rw [power_curve_fderiv hg,normalizedPrimitive_power hz hh0]
  have h1 : z⁻¹ * (Complex.I*z) = Complex.I := by field_simp
  rw [h1,Complex.I_im,mul_one]
  congr 1
  have hd : HasFDerivAt (fun y : ℂ => h y⁻¹)
      ((fderiv ℝ h z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hh.hasFDerivAt.comp z hi.hasFDerivAt
  rw [hd.fderiv,ContinuousLinearMap.comp_apply,complex_inv_fderiv_real hz]
  have h2 : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [h2]

 

theorem normalizedPrimitive_pole_angular_limit {n : ℕ} {u h : ℂ → Phase n}
    (hh : ContDiffAt ℝ ∞ h 0) (hh0 : h 0 ≠ 0) (m : ℕ)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => z^m • h z⁻¹) :
    Tendsto (fun z : ℂ => normalizedPrimitive (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 ((m:ℝ) / (2 * Real.pi))) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hdh := (hh.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => normalizedPrimitive (h z⁻¹))
      (cocompact ℂ) (𝓝 (normalizedPrimitive (h 0))) :=
    (normalizedPrimitive_smoothAt hh0).continuousAt.tendsto.comp (hh.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => (m:ℝ) / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 ((m:ℝ) / (2 * Real.pi))) := by
    simpa only [Function.comp_def,map_zero,add_zero] using
      ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
        (hprim.prodMk_nhds hvec)).const_add ((m:ℝ) / (2 * Real.pi))
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => y^m • h y⁻¹ := by
    obtain ⟨K,hK,hKs⟩ := mem_cocompact.mp he
    filter_upwards [hK.compl_mem_cocompact] with z hz
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hKs hy
  have hn : ∀ᶠ w in 𝓝 (0:ℂ), h w ≠ 0 :=
    hh.continuousAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hh0)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    ((hh.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun _ hw => hw.differentiableAt (by simp))
  apply hl.congr'
  filter_upwards [hnear,hi.eventually hn,hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hez hnz hdz hz
  rw [hez.self_of_nhds,hez.fderiv_eq]
  exact (normalizedPrimitive_pole_infinity_curve hz hdz hnz m).symm

 

theorem pole_norm_tendsto {n : ℕ} {u h : ℂ → Phase n}
    (hh : ContinuousAt h 0) (hh0 : h 0 ≠ 0) {m : ℕ} (hm : 0 < m)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => z^m • h z⁻¹) :
    Tendsto (fun z => ‖u z‖) (cocompact ℂ) atTop := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hp : 0 < ‖h 0‖ / 2 := half_pos (norm_pos_iff.mpr hh0)
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖h 0‖ / 2 < ‖h z⁻¹‖ :=
    (tendsto_order.mp (hh.tendsto.comp hi).norm).1 _ (by linarith)
  have hb : (fun z : ℂ => (‖h 0‖ / 2) * ‖z‖) ≤ᶠ[cocompact ℂ] fun z => ‖u z‖ := by
    filter_upwards [he,hev,tendsto_norm_cocompact_atTop.eventually_ge_atTop (1:ℝ)] with z hz hv hn
    rw [hz,norm_smul,norm_pow]
    calc
      (‖h 0‖ / 2) * ‖z‖ ≤ ‖h z⁻¹‖ * ‖z‖ := mul_le_mul_of_nonneg_right hv.le (norm_nonneg _)
      _ ≤ ‖h z⁻¹‖ * ‖z‖^m := mul_le_mul_of_nonneg_left
        (le_self_pow₀ hn (Nat.ne_of_gt hm)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  exact tendsto_atTop_mono' _ hb
    (Tendsto.const_mul_atTop hp tendsto_norm_cocompact_atTop)

 

theorem pole_radial_area {n : ℕ} {J : Phase n → End n}
    (hJ : ∀ x, Compatible (J x)) {S T : ℝ} (hST : S < T) (hT : T < 1)
    (houtside : ∀ x, S < capacity x → J x = standardJ n)
    {u h : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (huh : ∀ z, PseudoHolomorphicAt J u z)
    (hh : ContDiffAt ℝ ∞ h 0) (hh0 : h 0 ≠ 0) {m : ℕ} (hm : 0 < m)
    (he : u =ᶠ[cocompact ℂ] fun z : ℂ => z^m • h z⁻¹) :
    Integrable (curveDensity S T u) ∧ (∫ z, curveDensity S T u z) = (m:ℝ) := by
  have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  have huinf : Tendsto u (cocompact ℂ) (cocompact (Phase n)) := by
    rw [←Metric.cobounded_eq_cocompact (α := Phase n),←tendsto_norm_atTop_iff_cobounded]
    exact pole_norm_tendsto hh.continuousAt hh0 hm he
  have hul : Tendsto (realCurve u) (cocompact Plane) (cocompact (Phase n)) := huinf.comp hr
  have hn : Tendsto (fun z : Plane => planarPullback (realCurve u) normalizedPrimitive z
      (planeRotation z)) (cocompact Plane) (𝓝 ((m:ℝ) / (2 * Real.pi))) := by
    have ht := (normalizedPrimitive_pole_angular_limit hh hh0 m he).comp hr
    apply ht.congr
    intro z
    change normalizedPrimitive _ _ = normalizedPrimitive _ _
    have hd := realCurve_fderiv (z := z) (hu.differentiable (by simp) _) (planeRotation z)
    rw [equivRealProd_rotation] at hd
    exact congrArg (normalizedPrimitive (u (Complex.equivRealProdCLM.symm z))) hd.symm
  have hmom : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)))
      (cocompact Plane) (𝓝 1) :=
    (radialMoment_tendsto_one hST).comp ((capacity_tendsto_atTop n).comp hul)
  have hlim : Tendsto (fun z : Plane => curvePrimitive S T u z (planeRotation z))
      (cocompact Plane) (𝓝 ((m:ℝ) / (2 * Real.pi))) := by
    have ht : Tendsto (fun z : Plane => radialMoment S T (capacity (realCurve u z)) *
        planarPullback (realCurve u) normalizedPrimitive z (planeRotation z))
        (cocompact Plane) (𝓝 ((m:ℝ) / (2 * Real.pi))) := by
      simpa only [one_mul] using hmom.mul hn
    apply ht.congr'
    filter_upwards [hul.eventually (isCompact_singleton (x := (0 : Phase n))).compl_mem_cocompact] with z hz
    change _ = planarPullback (realCurve u) (radialPrimitiveCLM S T) z (planeRotation z)
    unfold planarPullback
    rw [radialPrimitiveCLM_eq_moment S T hz]
    rfl
  have hcureq : planarCurl (curvePrimitive S T u) = curveDensity S T u :=
    funext (curvePrimitive_curl hST hu)
  have hh := integral_planarCurl_of_nonneg_of_angular_limit
    (curvePrimitive_smooth hST hu)
    (by simpa only [hcureq] using curveDensity_nonneg hST hT hJ houtside huh) hlim
  rw [hcureq] at hh
  convert hh using 1
  field_simp

end HigherDimensionalBallPacking.Rigidity

end

end OAI
