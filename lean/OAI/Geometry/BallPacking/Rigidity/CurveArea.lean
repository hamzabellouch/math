import Mathlib
import OAI.Geometry.BallPacking.Rigidity.PlanarResidueCutoff

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def realCurve {n : ℕ} (u : ℂ → Phase n) : Plane → Phase n :=
  u ∘ Complex.equivRealProdCLM.symm

theorem realCurve_smooth {n : ℕ} {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (realCurve u) := hu.comp Complex.equivRealProdCLM.symm.contDiff

theorem realCurve_fderiv {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : DifferentiableAt ℝ u (Complex.equivRealProdCLM.symm z)) (v : Plane) :
    fderiv ℝ (realCurve u) z v =
      fderiv ℝ u (Complex.equivRealProdCLM.symm z) (Complex.equivRealProdCLM.symm v) := by
  rw [realCurve, fderiv_comp z hu Complex.equivRealProdCLM.symm.differentiableAt]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]

theorem realCurve_CR {n : ℕ} {J : Phase n → End n} {u : ℂ → Phase n} {z : Plane}
    (hu : PseudoHolomorphicAt J u (Complex.equivRealProdCLM.symm z)) :
    fderiv ℝ (realCurve u) z (0,1) =
      J (realCurve u z) (fderiv ℝ (realCurve u) z (1,0)) := by
  rw [realCurve_fderiv hu.1,realCurve_fderiv hu.1]
  simpa only [Complex.equivRealProdCLM_symm_apply, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul,one_mul,add_zero,zero_add,mul_one,realCurve,Function.comp_def] using hu.2 1

def planarPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Plane → E) (α : E → E →L[ℝ] ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  (α (v z)).comp (fderiv ℝ v z)

theorem planarPullback_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (planarPullback v α) :=
  (hα.comp hv).clm_comp (hv.fderiv_right (by simp))

def oneForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : E → E →L[ℝ] ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ 0 (α x)

theorem oneForm_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (oneForm α) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hα

theorem planarCurl_eq_extDeriv {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] := by
  rw [extDeriv_apply ((oneForm_smooth hα).differentiable (by simp) z)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change planarCurl α z =
    fderiv ℝ (fun y => α y (0,1)) z (1,0) - fderiv ℝ (fun y => α y (1,0)) z (0,1)
  rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _),
    fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add]
  rfl

theorem planarPullback_curl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl (planarPullback v α) z =
      extDeriv (oneForm α) (v z) ![fderiv ℝ v z (1,0), fderiv ℝ v z (0,1)] := by
  rw [planarCurl_eq_extDeriv (planarPullback_smooth hv hα)]
  have he : oneForm (planarPullback v α) = fun y =>
      (oneForm α (v y)).compContinuousLinearMap (fderiv ℝ v y) := by
    funext y
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smooth hα).differentiable (by simp) (v z))
    hv.contDiffAt (by
      norm_num [minSmoothness])]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

def curveDensity {n : ℕ} (σ τ : ℝ) (u : ℂ → Phase n) (z : Plane) : ℝ :=
  radialForm σ τ (realCurve u z)
    (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve u) z (0,1))

def curvePrimitive {n : ℕ} (σ τ : ℝ) (u : ℂ → Phase n) : Plane → Plane →L[ℝ] ℝ :=
  planarPullback (realCurve u) (radialPrimitiveCLM σ τ)

theorem curvePrimitive_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (curvePrimitive σ τ u) :=
  planarPullback_smooth (realCurve_smooth hu) (radialPrimitiveCLM_smooth hστ)

theorem curvePrimitive_curl {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    planarCurl (curvePrimitive σ τ u) z = curveDensity σ τ u z := by
  rw [curvePrimitive,planarPullback_curl (realCurve_smooth hu) (radialPrimitiveCLM_smooth hστ)]
  exact radialForm_extDeriv hστ _ _ _

theorem curveDensity_smooth {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (curveDensity σ τ u) := by
  have he : curveDensity σ τ u = planarCurl (curvePrimitive σ τ u) :=
    funext fun z => (curvePrimitive_curl hστ hu z).symm
  rw [he]
  exact SymplecticBallPacking.Hamiltonian.planarCurl_contDiff (curvePrimitive_smooth hστ hu)

theorem curveDensity_nonneg {n : ℕ} {σ τ : ℝ} (hστ : σ < τ) (hτ : τ < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (houtside : ∀ x, σ < capacity x → J x = standardJ n)
    {u : ℂ → Phase n} (hu : ∀ w, PseudoHolomorphicAt J u w) (z : Plane) :
    0 ≤ curveDensity σ τ u z := by
  unfold curveDensity
  rw [realCurve_CR (hu _)]
  by_cases hz : fderiv ℝ (realCurve u) z (1,0) = 0
  · simp only [hz,map_zero,radialForm,standardForm,Pi.zero_apply,
      Complex.zero_re,Complex.zero_im,mul_zero,sub_self,Finset.sum_const_zero,
      add_zero]
    exact le_refl _
  · exact (radialForm_adapted_pos hστ hτ hJ houtside _ hz).le


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def blowupSize (σ τ : ℝ) : ℝ := τ - radialOffset σ τ τ

def blowupMoment (σ τ t : ℝ) : ℝ := blowupSize σ τ + radialOffset σ τ t

theorem blowupMoment_smooth (σ τ : ℝ) : ContDiff ℝ ∞ (blowupMoment σ τ) :=
  contDiff_const.add (radialOffset_smooth σ τ)

theorem blowupMoment_hasDerivAt (σ τ t : ℝ) :
    HasDerivAt (blowupMoment σ τ) (radialSwitch σ τ t) t :=
  (radialOffset_hasDerivAt σ τ t).const_add _

theorem blowupMoment_before {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    blowupMoment σ τ t = blowupSize σ τ := by
  rw [blowupMoment,radialOffset_zero hστ ht,add_zero]

theorem blowupMoment_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t) :
    blowupMoment σ τ t = t := by
  have hh := radialOffset_after hστ ht
  unfold radialShift at hh
  unfold blowupMoment blowupSize
  linarith

theorem radialOffset_sub_id_antitone (σ τ : ℝ) :
    Antitone (fun t => radialOffset σ τ t - t) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun t => (radialOffset_hasDerivAt σ τ t).sub (hasDerivAt_id t))
  intro t
  change radialSwitch σ τ t - 1 ≤ 0
  linarith [radialSwitch_le_one σ τ t]

theorem blowupMoment_ge_id {σ τ : ℝ} (hστ : σ < τ) (t : ℝ) :
    t ≤ blowupMoment σ τ t := by
  by_cases ht : τ ≤ t
  · rw [blowupMoment_after hστ ht]
  · have hh := radialOffset_sub_id_antitone σ τ (le_of_not_ge ht)
    unfold blowupMoment blowupSize
    linarith

theorem blowupSize_bounds {σ τ : ℝ} (hστ : σ < τ) :
    σ ≤ blowupSize σ τ ∧ blowupSize σ τ ≤ τ := by
  constructor
  · simpa only [blowupMoment_before hστ le_rfl] using blowupMoment_ge_id hστ σ
  · unfold blowupSize
    linarith [radialOffset_nonneg hστ τ]

def blowupCoefficient (σ τ t : ℝ) : ℝ := blowupMoment σ τ t / t

def blowupSlope (σ τ t : ℝ) : ℝ :=
  (t * radialSwitch σ τ t - blowupMoment σ τ t) / t^2

theorem blowupCoefficient_smoothAt (σ τ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ContDiffAt ℝ ∞ (blowupCoefficient σ τ) t :=
  (blowupMoment_smooth σ τ).contDiffAt.div contDiffAt_id ht

theorem blowupCoefficient_hasDerivAt (σ τ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (blowupCoefficient σ τ) (blowupSlope σ τ t) t := by
  have h := (blowupMoment_hasDerivAt σ τ t).div (hasDerivAt_id t) ht
  simpa [blowupCoefficient,blowupSlope,mul_comm] using! h

theorem blowupCoefficient_before {σ τ t : ℝ} (hστ : σ < τ) (ht : t ≤ σ) :
    blowupCoefficient σ τ t = blowupSize σ τ / t := by
  rw [blowupCoefficient,blowupMoment_before hστ ht]

theorem blowupCoefficient_after {σ τ t : ℝ} (hστ : σ < τ) (ht : τ ≤ t)
    (ht0 : t ≠ 0) : blowupCoefficient σ τ t = 1 := by
  rw [blowupCoefficient,blowupMoment_after hστ ht,div_self ht0]

theorem blowupSlope_nonpos {σ τ t : ℝ} (hστ : σ < τ) (ht : 0 ≤ t) :
    blowupSlope σ τ t ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (radialSwitch_le_one σ τ t) ht
  have hq := blowupMoment_ge_id hστ t
  linarith

theorem blowup_radial_derivative {σ τ t : ℝ} (ht : t ≠ 0) :
    blowupCoefficient σ τ t + t * blowupSlope σ τ t = radialSwitch σ τ t := by
  unfold blowupCoefficient blowupSlope
  field_simp
  ring

def weightedTwoForm {n : ℕ} (g dg : ℝ) (x v w : Phase n) : ℝ :=
  g * standardForm v w + Real.pi * dg *
    (stdDot n x v * standardForm x w - stdDot n x w * standardForm x v)

theorem weightedTwoForm_J_nonneg {n : ℕ} {g dg : ℝ} (hdg : dg ≤ 0)
    (x v : Phase n) (hr : 0 ≤ g + capacity x * dg) :
    0 ≤ weightedTwoForm g dg x v (standardJ n v) := by
  have hcs := stdDot_standardForm_sq_le x v
  have hs : Real.pi * dg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hdg
  have hm := mul_le_mul_of_nonpos_left hcs hs
  have hh := mul_nonneg hr (stdDot_nonneg v)
  simp only [weightedTwoForm,standardForm_J_right,stdDot_J_right]
  rw [capacity_eq_stdDot] at hh
  nlinarith only [hm,hh]

theorem blowupForm_J_nonneg {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : 0 < capacity x) (v : Phase n) :
    0 ≤ weightedTwoForm (blowupCoefficient σ τ (capacity x))
      (blowupSlope σ τ (capacity x)) x v (standardJ n v) := by
  apply weightedTwoForm_J_nonneg (blowupSlope_nonpos hστ hx.le)
  rw [blowup_radial_derivative hx.ne']
  exact radialSwitch_nonneg σ τ _




theorem inverse_chart_analyticAt {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f)
    {J : Phase n → End n} {u : ℂ → Phase n} {z : ℂ}
    (hu : ∀ w, PseudoHolomorphicAt J u w) (hz : u z ∈ f '' U)
    (hJ : ∀ᶠ y in 𝓝 (u z), J y = imageJ U f y) :
    AnalyticAt ℂ (invFunOn f U ∘ u) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hc := (hu z).1.continuousAt
  filter_upwards [hc.eventually hJ,
    hc.eventually ((symplecticOn_open_image hf).mem_nhds hz)] with w hJw hw
  apply inverse_chart_holomorphic hf _ hw
  refine ⟨(hu w).1,?_⟩
  intro v
  rw [(hu w).2, hJw]

theorem inverse_chart_zero_iff {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {y : Phase n} (hy : y ∈ f '' U) :
    invFunOn f U y = 0 ↔ y = f 0 := by
  constructor
  · intro he
    have hi := invFunOn_eq hy
    rw [he] at hi
    exact hi.symm
  · rintro rfl
    exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0

theorem not_locally_constant_in_chart {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ∀ w, PseudoHolomorphicAt J u w)
    (hnc : ¬ ∀ w, u w = f 0)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y) (z : ℂ) :
    ¬ ∀ᶠ w in 𝓝 z, u w = f 0 := by
  let S : Set ℂ := {w | ∀ᶠ v in 𝓝 w, u v = f 0}
  have hcont : Continuous u := continuous_iff_continuousAt.mpr fun w => (hu w).1.continuousAt
  have hsub : S ⊆ {w | u w = f 0} := fun w hw => hw.self_of_nhds
  have hclosed : closure S ⊆ S := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact hwS
    have hew : u w = f 0 :=
      ((isClosed_eq hcont continuous_const).closure_subset_iff.mpr hsub) hw
    have haf : AnalyticAt ℂ (invFunOn f U ∘ u) w :=
      inverse_chart_analyticAt hf hu (hew ▸ mem_image_of_mem f h0) (hew ▸ hJ)
    have hcl : w ∈ closure ({v | u v = f 0} \ {w}) := by
      apply closure_mono _ hw
      intro v hv
      refine ⟨hsub hv,?_⟩
      intro hvw
      have : v = w := hvw
      subst v
      exact hwS hv
    have hfreq : ∃ᶠ v in 𝓝[≠] w, (invFunOn f U ∘ u) v = 0 := by
      apply (mem_closure_ne_iff_frequently_within.mp hcl).mono
      intro v hv
      change invFunOn f U (u v) = 0
      rw [hv]
      exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0
    have hzero := haf.frequently_zero_iff_eventually_zero.mp hfreq
    have hfU : f '' U ∈ 𝓝 (u w) :=
      (symplecticOn_open_image hf).mem_nhds (hew ▸ mem_image_of_mem f h0)
    filter_upwards [hzero, (hcont.continuousAt.eventually hfU)] with v hv hvU
    exact (inverse_chart_zero_iff hf h0 hvU).mp hv
  have hclopen : IsClopen S := ⟨isClosed_of_closure_subset hclosed,
    isOpen_setOfPred_eventually_nhds⟩
  intro hz
  have hall : S = univ := hclopen.eq_univ ⟨z,hz⟩
  apply hnc
  intro w
  exact hsub (hall ▸ mem_univ w)

theorem isolated_chart_centre {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ∀ w, PseudoHolomorphicAt J u w) (hnc : ¬ ∀ w, u w = f 0)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y)
    {z : ℂ} (hz : u z = f 0) :
    ∀ᶠ w in 𝓝[≠] z, u w ≠ f 0 := by
  have haf := inverse_chart_analyticAt hf hu (hz ▸ mem_image_of_mem f h0) (hz ▸ hJ)
  have hzero : ¬ ∀ᶠ w in 𝓝 z, (invFunOn f U ∘ u) w = 0 := by
    intro he
    apply not_locally_constant_in_chart hf h0 hu hnc hJ z
    have hU := (hu z).1.continuousAt.eventually
      ((symplecticOn_open_image hf).mem_nhds (hz ▸ mem_image_of_mem f h0))
    filter_upwards [he,hU] with w hw hwU
    exact (inverse_chart_zero_iff hf h0 hwU).mp hw
  have he := haf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hzero
  filter_upwards [he] with w hw
  intro heq
  apply hw
  change invFunOn f U (u w) = 0
  rw [heq]
  exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0

theorem chart_centre_positive_order {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ∀ w, PseudoHolomorphicAt J u w) (hnc : ¬ ∀ w, u w = f 0)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y)
    {z : ℂ} (hz : u z = f 0) :
    ∃ (m : ℕ) (v : ℂ → Phase n), 0 < m ∧ AnalyticAt ℂ v z ∧ v z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, (invFunOn f U ∘ u) w = (w-z)^m • v w := by
  have haf := inverse_chart_analyticAt hf hu (hz ▸ mem_image_of_mem f h0) (hz ▸ hJ)
  have hzero : ¬ ∀ᶠ w in 𝓝 z, (invFunOn f U ∘ u) w = 0 := by
    intro he
    apply not_locally_constant_in_chart hf h0 hu hnc hJ z
    have hU := (hu z).1.continuousAt.eventually
      ((symplecticOn_open_image hf).mem_nhds (hz ▸ mem_image_of_mem f h0))
    filter_upwards [he,hU] with w hw hwU
    exact (inverse_chart_zero_iff hf h0 hwU).mp hw
  obtain ⟨m,v,hv,hv0,he⟩ := haf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
  refine ⟨m,v,?_,hv,hv0,he⟩
  by_contra hm
  have hm0 : m = 0 := by omega
  have he0 := he.self_of_nhds
  have hi : (invFunOn f U ∘ u) z = 0 := by
    change invFunOn f U (u z) = 0
    rw [hz]
    exact (symplecticOn_injOn hf).leftInvOn_invFunOn h0
  rw [hi,hm0,pow_zero,one_smul] at he0
  exact hv0 he0.symm

theorem AffineLineCurve.not_constant {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (y : Phase n) : ¬ ∀ z, u z = y := by
  intro hc
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have ht : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 0) := by
    simpa only [hc, zero_smul] using hi.smul_const y
  exact hv (tendsto_nhds_unique hlim ht)

theorem AffineLineCurve.finite_centre_fibre {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) (h0 : (0 : Phase n) ∈ U)
    {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u)
    (hJ : ∀ᶠ y in 𝓝 (f 0), J y = imageJ U f y) :
    Set.Finite {z | u z = f 0} := by
  have hc : IsCompact {z | u z = f 0} :=
    hu.isProperMap.isCompact_preimage isCompact_singleton
  apply hc.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  have he := isolated_chart_centre hf h0 hu.2.1 (hu.not_constant _) hJ hz
  exact Filter.inf_principal_eq_bot.mpr he



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)

theorem capacity_smul_complex {n : ℕ} (c : ℂ) (x : Phase n) :
    capacity (c • x) = Complex.normSq c * capacity x := by
  simp only [capacity,Pi.smul_apply,smul_eq_mul,Complex.normSq_mul,Finset.mul_sum]
  ring_nf

theorem standardForm_smul_complex_same {n : ℕ} (c : ℂ) (x v : Phase n) :
    standardForm (c • x) (c • v) = Complex.normSq c * standardForm x v := by
  simp only [standardForm,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Finset.mul_sum,Complex.normSq_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem standardForm_smul_complex_self {n : ℕ} (c d : ℂ) (x : Phase n) :
    standardForm (c • x) (d • x) = (star c * d).im * stdDot n x x := by
  simp only [standardForm,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    stdDot_apply,Finset.mul_sum,Complex.star_def,Complex.conj_re,Complex.conj_im]
  apply Finset.sum_congr rfl
  intro i _
  ring

def normalizedPrimitive {n : ℕ} (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (1 / (2 * capacity x)) • stdOmega n x

@[simp] theorem normalizedPrimitive_apply {n : ℕ} (x v : Phase n) :
    normalizedPrimitive x v = standardForm x v / (2 * capacity x) := by
  simp only [normalizedPrimitive,smul_apply,smul_eq_mul,stdOmega_apply]
  ring

theorem capacity_pos {n : ℕ} {x : Phase n} (hx : x ≠ 0) : 0 < capacity x := by
  rw [capacity_eq_stdDot]
  exact mul_pos Real.pi_pos (stdDot_pos hx)

theorem normalizedPrimitive_smoothAt {n : ℕ} {x : Phase n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (@normalizedPrimitive n) x :=
  (contDiffAt_const.div (contDiffAt_const.mul (capacity_smooth n).contDiffAt)
    (mul_ne_zero (by norm_num) (capacity_pos hx).ne')).smul (stdOmega n).contDiff.contDiffAt

theorem normalizedPrimitive_smul {n : ℕ} {c : ℂ} (hc : c ≠ 0)
    {x : Phase n} (hx : x ≠ 0) (d : ℂ) (v : Phase n) :
    normalizedPrimitive (c • x) (d • x + c • v) =
      (c⁻¹ * d).im / (2 * Real.pi) + normalizedPrimitive x v := by
  rw [normalizedPrimitive_apply,←stdOmega_apply,map_add,stdOmega_apply,stdOmega_apply,
    standardForm_smul_complex_self,standardForm_smul_complex_same,
    capacity_smul_complex,normalizedPrimitive_apply,capacity_eq_stdDot]
  have hn : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hx' : stdDot n x x ≠ 0 := (stdDot_pos hx).ne'
  have he : (c⁻¹ * d).im = (star c * d).im / Complex.normSq c := by
    simp only [Complex.mul_im,Complex.inv_re,Complex.inv_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [he]
  field_simp

theorem normalizedPrimitive_power {n : ℕ} {z : ℂ} (hz : z ≠ 0)
    {x : Phase n} (hx : x ≠ 0) (m : ℕ) (w : ℂ) (v : Phase n) :
    normalizedPrimitive (z^m • x) (((m:ℂ) * z^(m-1) * w) • x + z^m • v) =
      (m:ℝ) * (z⁻¹ * w).im / (2 * Real.pi) + normalizedPrimitive x v := by
  rw [normalizedPrimitive_smul (pow_ne_zero m hz) hx]
  congr 2
  by_cases hm : m = 0
  · simp [hm]
  · have he : (z^m)⁻¹ * ((m:ℂ) * z^(m-1) * w) = (m:ℂ) * (z⁻¹ * w) := by
      have hm' : m = (m-1)+1 := by omega
      conv_lhs => arg 1; rw [hm',pow_succ]
      field_simp
    rw [he]
    simp

theorem complex_winding_eq_angular {z : Plane} (_hz : z ≠ 0) (v : Plane) :
    ((Complex.equivRealProdCLM.symm z)⁻¹ * Complex.equivRealProdCLM.symm v).im =
      angularOneForm z v := by
  have hn : Complex.normSq (Complex.equivRealProdCLM.symm z) = radiusSq z := by
    simp [Complex.normSq_apply,Complex.equivRealProdCLM_symm_apply,radiusSq,pow_two]
  rw [angularOneForm,smul_apply,smul_eq_mul,planarArea_apply]
  simp only [Complex.mul_im,Complex.inv_re,Complex.inv_im,hn]
  simp only [Complex.equivRealProdCLM_symm_apply,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add]
  ring


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def weightedPrimitive {n : ℕ} (g : ℝ → ℝ) (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (g (capacity x) / 2) • stdOmega n x

theorem weightedPrimitive_smoothAt {n : ℕ} {g : ℝ → ℝ} {x : Phase n}
    (hg : ContDiffAt ℝ ∞ g (capacity x)) :
    ContDiffAt ℝ ∞ (weightedPrimitive g) x :=
  ((hg.comp x (capacity_smooth n).contDiffAt).div_const 2).smul
    (stdOmega n).contDiff.contDiffAt

theorem weightedPrimitive_differentiableAt {n : ℕ} {g : ℝ → ℝ} {x : Phase n}
    (hg : DifferentiableAt ℝ g (capacity x)) :
    DifferentiableAt ℝ (weightedPrimitive g) x :=
  ((hg.div_const (2 : ℝ)).comp x (capacity_hasFDerivAt x).differentiableAt).fun_smul
    (stdOmega n).differentiableAt

theorem weightedPrimitive_derivative {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    fderiv ℝ (weightedPrimitive g) x v w =
      (g (capacity x) / 2) * standardForm v w +
      Real.pi * dg * stdDot n x v * standardForm x w := by
  have hd := ((hg.div_const 2).comp_hasFDerivAt x (capacity_hasFDerivAt x)).smul
    (stdOmega n).hasFDerivAt
  change HasFDerivAt (weightedPrimitive g) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul,stdOmega_apply,Function.comp_def]
  ring

theorem weightedPrimitive_extDeriv {n : ℕ} {g : ℝ → ℝ} {dg : ℝ} {x : Phase n}
    (hg : HasDerivAt g dg (capacity x)) (v w : Phase n) :
    extDeriv (oneForm (weightedPrimitive g)) x ![v,w] = weightedTwoForm (g (capacity x)) dg x v w := by
  have hα := weightedPrimitive_differentiableAt hg.differentiableAt
  have hω : DifferentiableAt ℝ (oneForm (weightedPrimitive g)) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := Phase n) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => weightedPrimitive g y w) x v -
    fderiv ℝ (fun y => weightedPrimitive g y v) x w = _
  have he (a b : Phase n) :
      fderiv ℝ (fun y => weightedPrimitive g y a) x b =
        fderiv ℝ (weightedPrimitive g) x b a := by
    rw [fderiv_clm_apply hα (differentiableAt_const a)]
    simp
  rw [he w v,he v w,weightedPrimitive_derivative hg,weightedPrimitive_derivative hg,
    standardForm_skew w v]
  unfold weightedTwoForm
  ring

def blowupPrimitive {n : ℕ} (σ τ : ℝ) : Phase n → Phase n →L[ℝ] ℝ :=
  weightedPrimitive (blowupCoefficient σ τ)

theorem blowupPrimitive_smoothAt {n : ℕ} (σ τ : ℝ) {x : Phase n} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (@blowupPrimitive n σ τ) x :=
  weightedPrimitive_smoothAt (blowupCoefficient_smoothAt σ τ (capacity_pos hx).ne')

theorem blowupPrimitive_extDeriv {n : ℕ} (σ τ : ℝ) {x : Phase n} (hx : x ≠ 0)
    (v w : Phase n) :
    extDeriv (oneForm (blowupPrimitive σ τ)) x ![v,w] =
      weightedTwoForm (blowupCoefficient σ τ (capacity x))
        (blowupSlope σ τ (capacity x)) x v w :=
  weightedPrimitive_extDeriv (blowupCoefficient_hasDerivAt σ τ (capacity_pos hx).ne') v w

theorem blowupPrimitive_extDeriv_nonneg {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : x ≠ 0) (v : Phase n) :
    0 ≤ extDeriv (oneForm (blowupPrimitive σ τ)) x ![v,standardJ n v] := by
  rw [blowupPrimitive_extDeriv σ τ hx]
  exact blowupForm_J_nonneg hστ (capacity_pos hx) v

theorem blowupPrimitive_before {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : capacity x ≤ σ) :
    blowupPrimitive σ τ x = blowupSize σ τ • normalizedPrimitive x := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [blowupPrimitive,weightedPrimitive,smul_apply,smul_eq_mul,stdOmega_apply,
    blowupCoefficient_before hστ hx,normalizedPrimitive_apply]
  ring

theorem blowupPrimitive_after {n : ℕ} {σ τ : ℝ} (hστ : σ < τ)
    {x : Phase n} (hx : τ ≤ capacity x) (hx0 : x ≠ 0) :
    blowupPrimitive σ τ x = (1/2 : ℝ) • stdOmega n x := by
  simp only [blowupPrimitive,weightedPrimitive,
    blowupCoefficient_after hστ hx (capacity_pos hx0).ne']



end HigherDimensionalBallPacking.Rigidity
end

end OAI
