import Mathlib
import OAI.Geometry.BallPacking.Rigidity.CurveArea

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

def stdPrimitive {n : ℕ} (x : Phase n) : Phase n →L[ℝ] ℝ :=
  (1/2 : ℝ) • stdOmega n x

theorem stdPrimitive_smooth (n : ℕ) : ContDiff ℝ ∞ (@stdPrimitive n) :=
  (contDiff_const (c := (1/2 : ℝ))).smul (stdOmega n).contDiff

def inversePullback {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (α : Phase n → Phase n →L[ℝ] ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ :=
  (α (invFunOn f U y)).comp (fderiv ℝ (invFunOn f U) y)

theorem inversePullback_smoothAt {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    {α : Phase n → Phase n →L[ℝ] ℝ}
    (hα : ContDiffAt ℝ ∞ α (invFunOn f U y)) :
    ContDiffAt ℝ ∞ (inversePullback U f α) y := by
  have hg := (symplecticOn_inverse_smooth hf).contDiffAt
    ((symplecticOn_open_image hf).mem_nhds hy)
  exact (hα.comp y hg).clm_comp (hg.fderiv_right (by simp))

theorem inverse_fderiv_preserves_form {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    (v w : Phase n) :
    standardForm (fderiv ℝ (invFunOn f U) y v) (fderiv ℝ (invFunOn f U) y w) =
      standardForm v w := by
  rw [symplecticOn_inverse_fderiv hf hy]
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible hf (invFunOn_mem hy)
  rw [←he,ContinuousLinearMap.inverse_equiv]
  have h := hf.2.2.2 _ (invFunOn_mem hy) (e.symm v) (e.symm w)
  rw [←he] at h
  simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using h.symm

def chartCorrection {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (σ τ : ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ := by
  classical
  exact if y ∈ f '' U then inversePullback U f (fun x => blowupPrimitive σ τ x - stdPrimitive x) y
    else 0

theorem chartCorrection_eq_near {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    (σ τ : ℝ) :
    chartCorrection U f σ τ =ᶠ[𝓝 y]
      inversePullback U f (fun x => blowupPrimitive σ τ x - stdPrimitive x) := by
  filter_upwards [(symplecticOn_open_image hf).mem_nhds hy] with z hz
  simp only [chartCorrection, ite_eq_left hz]

theorem chartCorrection_zero_off {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} {σ τ : ℝ} (hτ : 0 < τ) (hστ : σ < τ)
    {y : Phase n} (hy : y ∉ f '' closedBall n τ) : chartCorrection U f σ τ y = 0 := by
  classical
  unfold chartCorrection
  split_ifs with h
  · have hcap : τ < capacity (invFunOn f U y) := by
      by_contra! hn
      exact hy ⟨invFunOn f U y,hn,invFunOn_eq h⟩
    have hne : invFunOn f U y ≠ 0 := by
      intro he
      simp only [he,capacity,Pi.zero_apply,Complex.normSq_zero,Finset.sum_const_zero,mul_zero] at hcap
      linarith
    simp only [inversePullback,blowupPrimitive_after hστ hcap.le hne,stdPrimitive,
      sub_self,ContinuousLinearMap.zero_comp]
  · rfl

theorem chartCorrection_support {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U) :
    tsupport (chartCorrection U f σ τ) ⊆ f '' closedBall n τ := by
  apply closure_minimal _ ((closedBall_isCompact n τ).image_of_continuousOn
    (hf.2.1.continuousOn.mono hsub)).isClosed
  intro y hy
  by_contra hn
  exact hy (chartCorrection_zero_off hτ hστ hn)

theorem chartCorrection_compact {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U) :
    HasCompactSupport (chartCorrection U f σ τ) :=
  ((closedBall_isCompact n τ).image_of_continuousOn
    (hf.2.1.continuousOn.mono hsub)).of_isClosed_subset (isClosed_tsupport _)
      (chartCorrection_support hf hτ hστ hsub)

theorem chartCorrection_zero_near {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U)
    {y : Phase n} (hy : y ∉ f '' closedBall n τ) :
    chartCorrection U f σ τ =ᶠ[𝓝 y] 0 := by
  have hK := ((closedBall_isCompact n τ).image_of_continuousOn
    (hf.2.1.continuousOn.mono hsub)).isClosed
  filter_upwards [hK.isOpen_compl.mem_nhds hy] with z hz
  exact chartCorrection_zero_off hτ hστ hz

theorem chartCorrection_smoothAt {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U)
    {y : Phase n} (hy : y ≠ f 0) :
    ContDiffAt ℝ ∞ (chartCorrection U f σ τ) y := by
  by_cases hU : y ∈ f '' U
  · apply ContDiffAt.congr_of_eventuallyEq _ (chartCorrection_eq_near hf hU σ τ)
    apply inversePullback_smoothAt hf hU
    apply ContDiffAt.sub _ (stdPrimitive_smooth n).contDiffAt
    apply blowupPrimitive_smoothAt
    intro he
    have hi := invFunOn_eq hU
    rw [he] at hi
    exact hy hi.symm
  · apply ContDiffAt.congr_of_eventuallyEq contDiffAt_const
    apply chartCorrection_zero_near hf hτ hστ hsub
    exact fun h => hU (image_mono hsub h)



open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)

theorem complex_power_fderiv_real (m : ℕ) (z w : ℂ) :
    fderiv ℝ (fun y : ℂ => y^m) z w = (m:ℂ) * z^(m-1) * w := by
  rw [((hasDerivAt_pow m z).hasFDerivAt.restrictScalars ℝ).fderiv]
  change w * ((m:ℂ) * z^(m-1)) = _
  ring

theorem power_curve_fderiv {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hh : DifferentiableAt ℝ h z) (m : ℕ) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y^m • h y) z w =
      ((m:ℂ) * z^(m-1) * w) • h z + z^m • fderiv ℝ h z w := by
  rw [fderiv_fun_smul (((hasDerivAt_pow m z).differentiableAt).restrictScalars ℝ) hh]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,
    complex_power_fderiv_real]
  module

theorem normalizedPrimitive_power_pullback {n : ℕ} {h : ℂ → Phase n} {z : Plane}
    (hh : DifferentiableAt ℝ h (Complex.equivRealProdCLM.symm z))
    (hh0 : h (Complex.equivRealProdCLM.symm z) ≠ 0) (hz : z ≠ 0) (m : ℕ) :
    planarPullback (realCurve (fun y : ℂ => y^m • h y)) normalizedPrimitive z =
      ((m:ℝ) / (2 * Real.pi)) • angularOneForm z +
        planarPullback (realCurve h) normalizedPrimitive z := by
  apply ContinuousLinearMap.ext
  intro w
  have hz' : Complex.equivRealProdCLM.symm z ≠ 0 := by
    intro he
    apply hz
    exact Complex.equivRealProdCLM.symm.injective (he.trans (map_zero _).symm)
  have hd : DifferentiableAt ℝ (fun y : ℂ => y^m • h y)
      (Complex.equivRealProdCLM.symm z) :=
    (((hasDerivAt_pow m _).differentiableAt).restrictScalars ℝ).fun_smul hh
  change normalizedPrimitive _ (fderiv ℝ (realCurve _) z w) =
    (m:ℝ) / (2*Real.pi) * angularOneForm z w +
      normalizedPrimitive _ (fderiv ℝ (realCurve _) z w)
  rw [realCurve_fderiv hd,realCurve_fderiv hh,power_curve_fderiv hh]
  change normalizedPrimitive ((Complex.equivRealProdCLM.symm z)^m • h _) _ = _
  rw [normalizedPrimitive_power hz' hh0,complex_winding_eq_angular hz]
  simp only [realCurve,Function.comp_def]
  ring

theorem normalizedPrimitive_branch_residue {n : ℕ} {v h : ℂ → Phase n} {m : ℕ}
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (he : v =ᶠ[𝓝 0] fun z : ℂ => z^m • h z) :
    ∀ᶠ z in 𝓝[≠] (0 : Plane),
      planarPullback (realCurve v) normalizedPrimitive z =
        ((m:ℝ) / (2 * Real.pi)) • angularOneForm z +
          planarPullback (realCurve h) normalizedPrimitive z := by
  have ht : Tendsto Complex.equivRealProdCLM.symm (𝓝 (0 : Plane)) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.equivRealProdCLM_symm_apply,Prod.fst_zero,Prod.snd_zero,
      Complex.ofReal_zero,zero_mul,zero_add] using
      (Complex.equivRealProdCLM.symm.continuous.tendsto (0 : Plane))
  have hreal : realCurve v =ᶠ[𝓝 (0 : Plane)] realCurve (fun z : ℂ => z^m • h z) := ht.eventually he
  have hn : ∀ᶠ w in 𝓝 (0 : ℂ), h w ≠ 0 :=
    hh.continuousAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hh0)
  have hd : ∀ᶠ w in 𝓝 (0 : ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  filter_upwards [((eventually_eventually_nhds.mpr hreal).filter_mono nhdsWithin_le_nhds),
    (ht.eventually hn).filter_mono nhdsWithin_le_nhds,
    (ht.eventually hd).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with z hz hez hdz hz0
  change realCurve v =ᶠ[𝓝 z] realCurve (fun w : ℂ => w^m • h w) at hz
  have hp : planarPullback (realCurve v) normalizedPrimitive z =
      planarPullback (realCurve (fun w : ℂ => w^m • h w)) normalizedPrimitive z := by
    unfold planarPullback
    rw [hz.self_of_nhds,hz.fderiv_eq]
  rw [hp]
  exact normalizedPrimitive_power_pullback hdz hez hz0 m


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)

theorem realCurve_smoothAt {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : ContDiffAt ℝ ∞ u (Complex.equivRealProdCLM.symm z)) :
    ContDiffAt ℝ ∞ (realCurve u) z :=
  hu.comp z Complex.equivRealProdCLM.symm.contDiff.contDiffAt

theorem planarPullback_smoothAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ} {z : Plane}
    (hv : ContDiffAt ℝ ∞ v z) (hα : ContDiffAt ℝ ∞ α (v z)) :
    ContDiffAt ℝ ∞ (planarPullback v α) z :=
  (hα.comp z hv).clm_comp (hv.fderiv_right (by simp))

@[simp] theorem realCurve_zero {n : ℕ} (u : ℂ → Phase n) : realCurve u 0 = u 0 := by
  simp [realCurve,Complex.equivRealProdCLM_symm_apply]

theorem normalizedPrimitive_remainder_smooth {n : ℕ} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0) :
    ContDiffAt ℝ ∞ (planarPullback (realCurve h) normalizedPrimitive) 0 := by
  apply planarPullback_smoothAt
  · apply realCurve_smoothAt
    simpa only [map_zero] using (hh.contDiffAt.restrict_scalars ℝ : ContDiffAt ℝ ∞ h 0)
  · apply normalizedPrimitive_smoothAt
    simpa using hh0

theorem blowup_branch_residue {n : ℕ} {v h : ℂ → Phase n} {m : ℕ}
    (hm : 0 < m) (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (he : v =ᶠ[𝓝 0] fun z : ℂ => z^m • h z)
    {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : Plane),
        planarPullback (realCurve v) (blowupPrimitive σ τ) z =
          ((blowupSize σ τ * (m:ℝ)) / (2 * Real.pi)) • angularOneForm z + β z := by
  let β : Plane → Plane →L[ℝ] ℝ :=
    fun z => blowupSize σ τ • planarPullback (realCurve h) normalizedPrimitive z
  refine ⟨β,?_,?_⟩
  · exact (contDiffAt_const (c := blowupSize σ τ)).smul
      (normalizedPrimitive_remainder_smooth hh hh0)
  have hv0 : v 0 = 0 := by
    have hh := he.self_of_nhds
    simpa only [zero_pow hm.ne',zero_smul] using hh
  have hvc : ContinuousAt v 0 :=
    (continuousAt_id.pow m |>.smul hh.continuousAt).congr_of_eventuallyEq he
  have hrvc : ContinuousAt (realCurve v) 0 := by
    unfold realCurve
    apply ContinuousAt.comp _ Complex.equivRealProdCLM.symm.continuous.continuousAt
    simpa only [map_zero] using hvc
  have hcap : capacity (realCurve v 0) < σ := by
    simpa [hv0,capacity] using hσ
  have hsmall : ∀ᶠ z in 𝓝 (0 : Plane), capacity (realCurve v z) < σ :=
    ((capacity_smooth n).continuous.continuousAt.comp hrvc).eventually
      (isOpen_Iio.mem_nhds hcap)
  filter_upwards [normalizedPrimitive_branch_residue hh hh0 he,
    hsmall.filter_mono nhdsWithin_le_nhds] with z hz hzsmall
  have hpb : planarPullback (realCurve v) (blowupPrimitive σ τ) z =
      blowupSize σ τ • planarPullback (realCurve v) normalizedPrimitive z := by
    unfold planarPullback
    rw [blowupPrimitive_before hστ hzsmall.le]
    rfl
  rw [hpb,hz,smul_add,smul_smul]
  change (blowupSize σ τ * ((m:ℝ)/(2*Real.pi))) • angularOneForm z + β z = _
  congr 2
  ring


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneForm_smoothAt {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : ContDiffAt ℝ ∞ α x) : ContDiffAt ℝ ∞ (oneForm α) x :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp x hα

theorem oneForm_extDeriv_apply {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (v w : E) :
    extDeriv (oneForm α) x ![v,w] = fderiv ℝ α x v w - fderiv ℝ α x w v := by
  have hω : DifferentiableAt ℝ (oneForm α) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => α y w) x v - fderiv ℝ (fun y => α y v) x w = _
  rw [fderiv_clm_apply hα (differentiableAt_const w),
    fderiv_clm_apply hα (differentiableAt_const v)]
  simp

theorem oneForm_extDeriv_sub {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) (v w : E) :
    extDeriv (oneForm (fun y => α y - β y)) x ![v,w] =
      extDeriv (oneForm α) x ![v,w] - extDeriv (oneForm β) x ![v,w] := by
  rw [oneForm_extDeriv_apply (hα.fun_sub hβ),oneForm_extDeriv_apply hα,
    oneForm_extDeriv_apply hβ,fderiv_fun_sub hα hβ]
  simp only [sub_apply]
  ring

theorem oneForm_extDeriv_add {α β : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) (v w : E) :
    extDeriv (oneForm (fun y => α y + β y)) x ![v,w] =
      extDeriv (oneForm α) x ![v,w] + extDeriv (oneForm β) x ![v,w] := by
  rw [oneForm_extDeriv_apply (hα.fun_add hβ),oneForm_extDeriv_apply hα,
    oneForm_extDeriv_apply hβ,fderiv_fun_add hα hβ]
  simp only [add_apply]
  ring

theorem oneForm_extDeriv_congr {α β : E → E →L[ℝ] ℝ} {x : E}
    (he : α =ᶠ[𝓝 x] β) : extDeriv (oneForm α) x = extDeriv (oneForm β) x := by
  have he' : oneForm α =ᶠ[𝓝 x] oneForm β := he.fun_comp _
  simp only [extDeriv,he'.fderiv_eq]

theorem planarCurl_eq_extDeriv_at {α : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hα : DifferentiableAt ℝ α z) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] :=
  (oneForm_extDeriv_apply hα _ _).symm

theorem planarPullback_curlAt {v : Plane → E} {α : E → E →L[ℝ] ℝ} {z : Plane}
    (hv : ContDiffAt ℝ ∞ v z) (hα : ContDiffAt ℝ ∞ α (v z)) :
    planarCurl (planarPullback v α) z =
      extDeriv (oneForm α) (v z) ![fderiv ℝ v z (1,0),fderiv ℝ v z (0,1)] := by
  rw [planarCurl_eq_extDeriv_at ((planarPullback_smoothAt hv hα).differentiableAt (by simp))]
  have he : oneForm (planarPullback v α) = fun y =>
      (oneForm α (v y)).compContinuousLinearMap (fderiv ℝ v y) := by
    funext y
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smoothAt hα).differentiableAt (by simp))
    hv (by
      norm_num [minSmoothness])]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem inversePullback_extDeriv {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    {α : Phase n → Phase n →L[ℝ] ℝ}
    (hα : ContDiffAt ℝ ∞ α (invFunOn f U y)) (v w : Phase n) :
    extDeriv (oneForm (inversePullback U f α)) y ![v,w] =
      extDeriv (oneForm α) (invFunOn f U y)
        ![fderiv ℝ (invFunOn f U) y v,fderiv ℝ (invFunOn f U) y w] := by
  have he : oneForm (inversePullback U f α) = fun z =>
      (oneForm α (invFunOn f U z)).compContinuousLinearMap (fderiv ℝ (invFunOn f U) z) := by
    funext z
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smoothAt hα).differentiableAt (by simp))
    ((symplecticOn_inverse_smooth hf).contDiffAt ((symplecticOn_open_image hf).mem_nhds hy)) (by
      norm_num [minSmoothness])]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem stdPrimitive_extDeriv {n : ℕ} (x v w : Phase n) :
    extDeriv (oneForm stdPrimitive) x ![v,w] = standardForm v w := by
  have he : (@stdPrimitive n) = weightedPrimitive (fun _ => 1) := rfl
  rw [he,weightedPrimitive_extDeriv (hasDerivAt_const (capacity x) (1 : ℝ))]
  simp [weightedTwoForm]

theorem chartCorrection_extDeriv {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    {y : Phase n} (hy : y ∈ f '' U) (hy0 : y ≠ f 0) (v w : Phase n) :
    extDeriv (oneForm (chartCorrection U f σ τ)) y ![v,w] =
      extDeriv (oneForm (blowupPrimitive σ τ)) (invFunOn f U y)
        ![fderiv ℝ (invFunOn f U) y v,fderiv ℝ (invFunOn f U) y w] - standardForm v w := by
  have hx : invFunOn f U y ≠ 0 := by
    intro he
    have hi := invFunOn_eq hy
    rw [he] at hi
    exact hy0 hi.symm
  have hα := blowupPrimitive_smoothAt σ τ hx
  have hβ := (stdPrimitive_smooth n).contDiffAt (x := invFunOn f U y)
  rw [oneForm_extDeriv_congr (chartCorrection_eq_near hf hy σ τ),
    inversePullback_extDeriv hf hy (hα.sub hβ),
    oneForm_extDeriv_sub (hα.differentiableAt (by simp)) (hβ.differentiableAt (by simp)),
    stdPrimitive_extDeriv,inverse_fderiv_preserves_form hf hy]

theorem inverse_fderiv_intertwines {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {y : Phase n} (hy : y ∈ f '' U)
    (v : Phase n) :
    fderiv ℝ (invFunOn f U) y (imageJ U f y v) =
      standardJ n (fderiv ℝ (invFunOn f U) y v) := by
  rw [symplecticOn_inverse_fderiv hf hy]
  unfold imageJ
  obtain ⟨e,he⟩ := symplecticOn_fderiv_invertible hf (invFunOn_mem hy)
  rw [←he]
  simp


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

def planeRotation (z : Plane) : Plane := (-z.2,z.1)

def outerProfile (A t : ℝ) : ℝ :=
  Real.smoothTransition (t+2) * (1 - Real.smoothTransition ((t-A)/A))

theorem outerProfile_smooth (A : ℝ) : ContDiff ℝ ∞ (outerProfile A) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const A)))

theorem outerProfile_compact {A : ℝ} (hA : 0 < A) : HasCompactSupport (outerProfile A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2*A))
  intro t ht
  have ht' : t < -2 ∨ 2*A < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases ht' with ht' | ht'
  · simp only [outerProfile,Real.smoothTransition.zero_of_nonpos (by linarith : t+2 ≤ 0),zero_mul]
  · have h : 1 ≤ (t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]

theorem outerProfile_nonneg (A t : ℝ) : 0 ≤ outerProfile A t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem outerProfile_zero_value {A : ℝ} (hA : 0 < A) : outerProfile A 0 = 1 := by
  have h : (0-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  simp only [outerProfile,zero_add,Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2),
    Real.smoothTransition.zero_of_nonpos h,sub_zero,mul_one]

theorem outerProfile_deriv {A t : ℝ} (ht : 0 ≤ t) :
    deriv (outerProfile A) t = -(deriv Real.smoothTransition ((t-A)/A) / A) := by
  have he : outerProfile A =ᶠ[𝓝 t] fun s => 1 - Real.smoothTransition ((s-A)/A) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : (-1:ℝ) < t)] with s hs
    have hs' : -1 < s := hs
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s + 2),one_mul]
  rw [he.deriv_eq]
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hh := (hs.differentiable (by simp) ((t-A)/A)).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const A).div_const A)
  have hd := hh.const_sub 1
  change HasDerivAt (fun s => 1 - Real.smoothTransition ((s-A)/A)) _ t at hd
  rw [hd.deriv]
  simp only [div_eq_mul_inv,one_mul]

theorem outerProfile_deriv_nonpos {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    deriv (outerProfile A) t ≤ 0 := by
  rw [outerProfile_deriv ht]
  exact neg_nonpos.mpr (div_nonneg Real.smoothTransition.monotone.deriv_nonneg hA.le)

theorem outerProfile_deriv_zero_before {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t < A) :
    deriv (outerProfile A) t = 0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1:ℝ) A from ⟨by linarith,htA⟩)] with s hs
    have hn : (s-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hA.le
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s + 2),
      Real.smoothTransition.zero_of_nonpos hn,sub_zero,mul_one]
  rw [he.deriv_eq,deriv_const]

theorem cutoffWedge_radial_rotation {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    cutoffWedge (fun y => g (radiusSq y)) β z =
      2 * deriv g (radiusSq z) * β z (planeRotation z) := by
  have hh := (hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)
  change HasFDerivAt (fun y => g (radiusSq y)) _ z at hh
  have he : planeRotation z = (-z.2) • ((1,0) : Plane) + z.1 • (0,1) := by
    ext <;> simp [planeRotation]
  unfold cutoffWedge
  rw [hh.fderiv, he,map_add,map_smul,map_smul]
  simp only [smul_apply,smul_eq_mul,planarDot_apply]
  simp only [mul_one,mul_zero,add_zero,zero_add]
  ring

theorem nonneg_angular_limit_of_nonneg_curl {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcurl : ∀ z, 0 ≤ planarCurl β z) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) : 0 ≤ k := by
  by_contra! hk
  have he : ∀ᶠ z in cocompact Plane, β z (planeRotation z) ≤ k/2 :=
    (hlim.eventually (eventually_lt_nhds (by linarith : k < k/2))).mono fun _ h => h.le
  obtain ⟨K,hK,hKsub⟩ := mem_cocompact.mp he
  obtain ⟨B,hB,hbound⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  let A := B+1
  have hA : 0 < A := by dsimp [A]; linarith
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hgc : HasCompactSupport g := outerProfile_compact hA
  have hcomp : ∀ z : Plane,
      2 * deriv g (radiusSq z) * (k/2) ≤ cutoffWedge (fun y => g (radiusSq y)) β z := by
    intro z
    rw [cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z) = 0
    · simp [hd]
    have hzA : A ≤ radiusSq z := by
      by_contra! h
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) h)
    have hzK : z ∉ K := by
      intro h
      have hb := hbound (radiusSq z) ⟨z,h,rfl⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (radiusSq_nonneg z)] at hb
      dsimp [A] at hzA
      linarith
    exact mul_le_mul_of_nonpos_left (hKsub hzK)
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z)))
  have hdi : Integrable (fun z : Plane => 2 * deriv g (radiusSq z) * (k/2)) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hgc.deriv)).const_mul 2).mul_const (k/2)
  have hwi := cutoffWedge_integrable (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ
  have hle := integral_mono hdi hwi hcomp
  have hg0 : g 0 = 1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hgc,hg0] at hle
  have hnonneg : 0 ≤ ∫ z : Plane, g (radiusSq z) * planarCurl β z :=
    integral_nonneg fun z => mul_nonneg (outerProfile_nonneg A _) (hcurl z)
  rw [integral_cutoffWedge (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ] at hle
  dsimp only [Function.comp_def] at hle
  have hpk := mul_neg_of_pos_of_neg Real.pi_pos hk
  nlinarith only [hle,hnonneg,hpk]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
