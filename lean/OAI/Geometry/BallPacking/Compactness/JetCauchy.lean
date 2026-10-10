import Mathlib
import OAI.Geometry.BallPacking.Compactness.GradientBounds

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance ljcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance ljcInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance ljcInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance ljcInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance ljcInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance ljcInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance ljcInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance ljcInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

lemma cauchy_coefficient_action {A : ℕ → HMap ℂ (E →L[ℝ] E)} {v : ℕ → HMap ℂ E}
    (hA : CauchySeq A) (hv : CauchySeq v) :
    CauchySeq (fun i => holderCoefficientAction (A i) (v i)) := by
  obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete hA
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete hv
  have hAc : Continuous (fun x : HMap ℂ (E →L[ℝ] E) => holderCoefficientAction x) :=
    (bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).continuous
  have hc : Continuous (fun p : HMap ℂ (E →L[ℝ] E) × HMap ℂ E =>
      holderCoefficientAction p.1 p.2) := (hAc.comp continuous_fst).clm_apply continuous_snd
  exact ((hc.tendsto (a,w)).comp (ha.prodMk_nhds hw)).cauchySeq

lemma cutoff_forcing_holder_cauchy (C D : HMap ℂ (E →L[ℝ] E))
    {A : ℕ → HMap ℂ (E →L[ℝ] E)} {v : ℕ → HMap ℂ E}
    (hA : CauchySeq A) (hv : CauchySeq v) :
    CauchySeq (fun i => holderCoefficientAction C (v i)-
      holderCoefficientAction (A i) (holderCoefficientAction D (v i))) := by
  have hC := cauchy_coefficient_action (E := E) (cauchySeq_const (x := C)) hv
  have hD := cauchy_coefficient_action (E := E) (cauchySeq_const (x := D)) hv
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨d,hd⟩ := cauchySeq_tendsto_of_complete (cauchy_coefficient_action hA hD)
  exact (hc.sub hd).cauchySeq

theorem cutoff_jet_cauchy (b : ContDiffBump (0:ℂ)) {L : ℝ} (hL : 0≤L) :
    ∃ δ : ℝ,0<δ ∧ ∀ (u : ℕ → ℂ → E) (hu : ∀ i,ContDiff ℝ ∞ (u i))
      (A : ℕ → ℂ → E →L[ℝ] E),
      (∀ i,Continuous (A i)) →(∀ i,u i 0=0) →
      (∀ i z,‖A i z‖≤δ) →
      (∀ i x y,‖A i x-A i y‖≤L*dist x y) →
      (∃ M H : ℝ,0≤M ∧ 0≤H ∧ (∀ i z,‖u i z‖≤M) ∧
        ∀ i x y,‖u i x-u i y‖≤H*dist x y) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖u i z-u j z‖≤ε) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖A i z-A j z‖≤ε) →
      (∀ i z,b z≠0 →fderiv ℝ (u i) z Complex.I-Complex.I • fderiv ℝ (u i) z 1=
        A i z (fderiv ℝ (u i) z 1)) →
      CauchySeq (fun i => cutoffCurveJet b (hu i)) := by
  obtain ⟨ε,hε,hcauchy⟩ := small_coefficient_cauchy (E := E) (isCompact_closedBall (0:ℂ) b.rOut)
  obtain ⟨δ,hδ,hsmall⟩ := holder_small_of_small_value (X := ℂ) (E := E →L[ℝ] E) hL hε
  refine ⟨δ,hδ,?_⟩
  intro u hu A hAc h0 hAb hAl hUb hUc hAcc hcr
  obtain ⟨M,H,hM,hH,hUb,hUl⟩ := hUb
  obtain ⟨B,hB,hD,hDL,hC,hCL⟩ := cutoff_transport_bounds (E := E) b
  let V : ℕ → HMap ℂ E := fun i => ofBoundedLipschitz (u i) (hu i).continuous M H hM hH (hUb i) (hUl i)
  let T : ℕ → HMap ℂ (E →L[ℝ] E) := fun i => ofBoundedLipschitz (A i) (hAc i) δ L hδ.le hL (hAb i) (hAl i)
  let C : HMap ℂ (E →L[ℝ] E) := ofBoundedLipschitz (cutoffCommute b)
    (cutoffCommute_smooth b).continuous B B hB.le hB.le hC hCL
  let D : HMap ℂ (E →L[ℝ] E) := ofBoundedLipschitz (cutoffTransport b 1)
    (cutoffTransport_smooth b 1).continuous B B hB.le hB.le hD hDL
  let f : ℕ → HMap ℂ E := fun i => holderCoefficientAction C (V i)-
    holderCoefficientAction (T i) (holderCoefficientAction D (V i))
  have hVc : CauchySeq V := holder_cauchy_of_uniform_values hH hUl hUc
  have hTc : CauchySeq T := holder_cauchy_of_uniform_values hL hAl hAcc
  have hfc : CauchySeq f := cutoff_forcing_holder_cauchy C D hTc hVc
  apply hcauchy (fun i => cutoffCurveJet b (hu i)) T f
    (fun i => cutoffCurveJet_zero b (hu i) (h0 i)) (fun i => cutoffCurveJet_supported b (hu i))
    (fun i => (hsmall (T i) (hAb i) (hAl i)).le) ?_ hTc hfc
  intro i
  apply cutoffCurveJet_CR b (hu i) (hcr i) (T i) (fun _ _ => rfl) (f i)
  intro z
  rfl


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance lsoInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance lsoInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance lsoInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance lsoInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance lsoInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance lsoInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance lsoInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance lsoInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance

lemma common_small_value_scale {L K d : ℝ} (hL : 0≤L) (hK : 0≤K) (hd : 0<d) :
    ∃ δ : ℝ,0<δ ∧ δ≤1 ∧ L*δ≤d ∧ K*δ≤d := by
  have hp : 0<L+K+1 := by linarith
  let δ := min 1 (d/(L+K+1))
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hd hp)
  have hm : (L+K+1)*δ≤d := by
    have h := (le_div_iff₀ hp).mp (min_le_right 1 (d/(L+K+1)))
    simpa only [mul_comm] using h
  refine ⟨δ,hδ,min_le_left _ _,?_,?_⟩ <;> nlinarith

omit [CompleteSpace E] in
lemma cutoffCurveJet_deriv_zero (b : ContDiffBump (0:ℂ)) {u : ℂ → E}
    (hu : ContDiff ℝ ∞ u) (h0 : u 0=0) :
    cDeriv (cutoffCurveJet b hu) 0=fderiv ℝ u 0 := by
  ext h
  rw [cutoffCurveJet_deriv,h0,smul_zero,zero_add,
    b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),one_smul]

theorem bounded_cutoff_gradient_small (b : ContDiffBump (0:ℂ))
    {L H η : ℝ} (hL : 0≤L) (hH : 0≤H) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ (F : E → E →L[ℝ] E),Continuous F → F 0=0 →
      (∀ x y,‖F x-F y‖≤L*‖x-y‖) → ∀ u : ℂ → E,ContDiff ℝ ∞ u → u 0=0 →
      (∀ z,‖u z‖≤δ) → (∀ x y,‖u x-u y‖≤H*dist x y) →
      (∀ z,b z≠0 → fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=
        F (u z) (fderiv ℝ u z 1)) → ‖fderiv ℝ u 0‖<η := by
  obtain ⟨B,hB,hD,hDL,hC,hCL⟩ := cutoff_transport_bounds (E := E) b
  let M : ℝ := B*(H+1)+L*(B*(H+1))+L*H*B
  have hM : 0≤M := by dsimp [M]; positivity
  obtain ⟨d,hd,hsmall⟩ := small_value_elliptic_estimate (E := E)
    (isCompact_closedBall (0:ℂ) b.rOut) (mul_nonneg hL hH) hM hη
  obtain ⟨δ,hδ,hδ1,hδA,hδf⟩ := common_small_value_scale hL
    (by positivity : 0≤(1+L)*B) hd
  refine ⟨δ,hδ,?_⟩
  intro F hF hF0 hFL u hu h0 hub hul hcr
  let A : ℂ → E →L[ℝ] E := fun z => F (u z)
  have hAc : Continuous A := hF.comp hu.continuous
  have hAb : ∀ z,‖A z‖≤L*δ := by
    intro z
    have hh := hFL (u z) 0
    rw [hF0,sub_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hub z) hL)
  have hAl : ∀ x y,‖A x-A y‖≤(L*H)*dist x y := by
    intro x y
    exact (hFL (u x) (u y)).trans ((mul_le_mul_of_nonneg_left (hul x y) hL).trans_eq (by ring))
  let ac : HMap ℂ (E →L[ℝ] E) := ofBoundedLipschitz A hAc (L*δ) (L*H)
    (mul_nonneg hL hδ.le) (mul_nonneg hL hH) hAb hAl
  have hbds := cutoff_forcing_bounds hδ.le hδ1 hH hL hB.le hub hul hAb hAl hC hCL hD hDL
  let g : ℂ → E := fun z => cutoffCommute b z (u z)-A z (cutoffTransport b 1 z (u z))
  have hgc : Continuous g := ((cutoffCommute_smooth b).continuous.clm_apply hu.continuous).sub
    (hAc.clm_apply ((cutoffTransport_smooth b 1).continuous.clm_apply hu.continuous))
  let f : HMap ℂ E := ofBoundedLipschitz g hgc (((1+L)*B)*δ) M
    (by positivity) hM hbds.1 hbds.2
  have hAe : ∀ z,valueCLM _ ac z=A z := fun _ => rfl
  have hfe : ∀ z,valueCLM _ f z=g z := fun _ => rfl
  have heq : standardJetCR (cutoffCurveJet b hu)=
      holderCoefficientAction ac (jetDirectional 1 (cutoffCurveJet b hu))+f := by
    apply cutoffCurveJet_CR b hu hcr ac (fun z _ => hAe z) f
    intro z
    rw [hfe,hAe]
    exact rfl
  have hh := hsmall (cutoffCurveJet b hu) (cutoffCurveJet_zero b hu h0)
    (cutoffCurveJet_supported b hu) ac f (fun z => (hAb z).trans hδA) hAl
    (fun z => (hbds.1 z).trans hδf) hbds.2 heq
  have hder : ‖fderiv ℝ u 0‖≤‖cutoffCurveJet b hu‖ := by
    rw [←cutoffCurveJet_deriv_zero b hu h0]
    exact c_deriv_bound _ _
  exact hder.trans_lt hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance legInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance legInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

omit [CompleteSpace E] in
lemma smooth_cutoff_local_bounds (b : ContDiffBump (0:ℂ)) {u : ℂ → E}
    (hu : ContDiff ℝ ∞ u) {R δ H : ℝ} (hR : b.rOut≤R) (hδ : 0≤δ) (hδ1 : δ≤1) (hH : 0≤H)
    (hb : ∀ z,‖z‖≤R → ‖u z‖≤δ) (hd : ∀ z,‖z‖≤R → ‖fderiv ℝ u z‖≤H) :
    ∃ K : ℝ,0≤K ∧ K=(boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport).bound ∧
    (∀ z,‖b z • u z‖≤δ) ∧
    (∀ z,‖fderiv ℝ (fun z => b z • u z) z‖≤H+K) := by
  let hs := boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport
  let K := hs.bound
  have hK : 0≤K := hs.bound_nonneg
  have hbn (z : ℂ) : ‖b z‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact b.le_one
  have hder (z : ℂ) : fderiv ℝ (fun z => b z • u z) z=
      b z • fderiv ℝ u z+(fderiv ℝ b z).smulRight (u z) :=
    fderiv_fun_smul (b.contDiff.differentiable (by simp : (∞ : WithTop ℕ∞)≠0) z)
      (hu.differentiable (by simp : (∞ : WithTop ℕ∞)≠0) z)
  have hzouts (z : ℂ) (hz : ¬‖z‖≤R) : b z=0 ∧ fderiv ℝ b z=0 := by
    have hn : z∉tsupport b := by
      rw [b.tsupport_eq,Metric.mem_closedBall,dist_zero_right]
      exact fun hh => hz (hh.trans hR)
    exact ⟨image_eq_zero_of_notMem_tsupport hn,fderiv_of_notMem_tsupport ℝ hn⟩
  refine ⟨K,hK,rfl,?_,?_⟩
  · intro z
    by_cases hz : ‖z‖≤R
    · rw [norm_smul]
      exact (mul_le_mul (hbn z) (hb z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · rw [(hzouts z hz).1,zero_smul,norm_zero]; exact hδ
  · intro z
    by_cases hz : ‖z‖≤R
    · rw [hder]
      have h1 : ‖b z • fderiv ℝ u z‖≤H := by
        rw [norm_smul]
        exact (mul_le_mul (hbn z) (hd z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      have h2 : ‖(fderiv ℝ b z).smulRight (u z)‖≤K := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        have h := mul_le_mul (hs.norm_fderiv_le z) (hb z hz) (norm_nonneg _) hK
        exact h.trans (by nlinarith)
      exact (norm_add_le _ _).trans (add_le_add h1 h2)
    · rw [hder,(hzouts z hz).1,(hzouts z hz).2]
      simp only [zero_smul,ContinuousLinearMap.zero_smulRight,add_zero,norm_zero]
      positivity

theorem local_nonlinear_gradient_small {L H η : ℝ} (hL : 0≤L) (hH : 0≤H) (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ (F : E → E →L[ℝ] E),Continuous F → F 0=0 →
      (∀ x y,‖F x-F y‖≤L*‖x-y‖) → ∀ u : ℂ → E,ContDiff ℝ ∞ u → u 0=0 →
      (∀ z,‖z‖≤2 → ‖u z‖≤δ) → (∀ z,‖z‖≤2 → ‖fderiv ℝ u z‖≤H) →
      (∀ z,‖z‖<2 → fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=
        F (u z) (fderiv ℝ u z 1)) → ‖fderiv ℝ u 0‖<η := by
  let b : ContDiffBump (0:ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  let c : ContDiffBump (0:ℂ) := ⟨1,3/2,by norm_num,by norm_num⟩
  let hc := boundedCThree_of_compactSupport c.contDiff c.hasCompactSupport
  have hH' : 0≤H+hc.bound := add_nonneg hH hc.bound_nonneg
  obtain ⟨d,hd,hsmall⟩ := bounded_cutoff_gradient_small (E := E) b hL hH' hη
  let δ := min d 1
  have hδ : 0<δ := lt_min hd zero_lt_one
  refine ⟨δ,hδ,?_⟩
  intro F hF hF0 hFL u hu h0 hb hdu hcr
  let w : ℂ → E := fun z => c z • u z
  have hw : ContDiff ℝ ∞ w := c.contDiff.smul hu
  have hw0 : w 0=0 := by simp only [w,h0,smul_zero]
  obtain ⟨K,hK,hKe,hwb,hwd⟩ := smooth_cutoff_local_bounds c hu (by change (3:ℝ)/2≤2; norm_num)
    hδ.le (min_le_right _ _) hH hb hdu
  have hwl : ∀ x y,‖w x-w y‖≤(H+hc.bound)*dist x y := by
    intro x y
    rw [dist_eq_norm]
    apply norm_sub_le_of_deriv_bound (hw.differentiable (by simp))
    intro z
    simpa only [hKe] using hwd z
  have hwne (z : ℂ) (hz : ‖z‖<1) : w =ᶠ[𝓝 z] u := by
    have he := c.eventuallyEq_one_of_mem_ball (show z∈Metric.ball (0:ℂ) c.rIn by
      simpa only [Metric.mem_ball,dist_zero_right] using hz)
    filter_upwards [he] with y hy
    change c y • u y=u y
    rw [hy]; exact one_smul ℝ (u y)
  have hcrw : ∀ z,b z≠0 → fderiv ℝ w z Complex.I-Complex.I • fderiv ℝ w z 1=
      F (w z) (fderiv ℝ w z 1) := by
    intro z hz
    have hz' : ‖z‖<(1:ℝ)/2 := by
      have hs : z∈Function.support b := hz
      rw [b.support_eq] at hs
      simpa only [Metric.mem_ball,dist_zero_right] using hs
    have he := hwne z (by linarith)
    rw [he.fderiv_eq,he.eq_of_nhds]
    exact hcr z (by linarith)
  have hh := hsmall F hF hF0 hFL w hw hw0 (fun z => (hwb z).trans (min_le_left _ _)) hwl hcrw
  rwa [(hwne 0 (by simp)).fderiv_eq] at hh


end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance djcInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance djcInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance djcInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance djcInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance

lemma uniform_cauchy_comp_lipschitz {X Y Z : Type*} [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] {F : ℕ → Y → Z} {u : ℕ → X → Y} {L M : ℝ}
    (hL : 0≤L) (hF : ∀ i x y,‖F i x-F i y‖≤L*‖x-y‖)
    (hb : ∀ i x,‖u i x‖≤M)
    (hu : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖u i x-u j x‖≤ε)
    (hFc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ y,‖y‖≤M →‖F i y-F j y‖≤ε) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x,‖F i (u i x)-F j (u j x)‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := hu (ε/(2*(L+1))) (div_pos hε (by linarith))
  obtain ⟨M,hM⟩ := hFc (ε/2) (half_pos hε)
  refine ⟨max N M,fun i hi j hj x => ?_⟩
  have h1 := hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) x
  have h2 := hM i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj) (u j x) (hb j x)
  have hp : 0<L+1 := by linarith
  have hscale : L*(ε/(2*(L+1)))≤ε/2 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have he : (2*(L+1))*(ε/(2*(L+1)))=ε := mul_div_cancel₀ ε (by positivity)
    have hd : 0≤ε/(2*(L+1)) := by positivity
    nlinarith
  have hbound : ‖F i (u i x)-F i (u j x)‖≤ε/2 :=
    (hF i _ _).trans ((mul_le_mul_of_nonneg_left h1 hL).trans hscale)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (by linarith)

omit [CompleteSpace E] in
lemma cutoff_uniform_cauchy (c : ContDiffBump (0:ℂ)) {R : ℝ} (hc : c.rOut≤R)
    {u : ℕ → ℂ → E}
    (hu : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤R →‖u i z-u j z‖≤ε) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖c z • u i z-c z • u j z‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := hu ε hε
  refine ⟨N,fun i hi j hj z => ?_⟩
  by_cases hz : ‖z‖≤R
  · rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg c.nonneg]
    exact (mul_le_mul c.le_one (hN i hi j hj z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · have hz' : z∉tsupport c := by
      rw [c.tsupport_eq,Metric.mem_closedBall,dist_zero_right]
      exact fun hh => hz (hh.trans hc)
    simp only [image_eq_zero_of_notMem_tsupport hz',zero_smul,sub_self,norm_zero]
    exact hε.le

def smallDiskBump : ContDiffBump (0:ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def largerDiskBump : ContDiffBump (0:ℂ) := ⟨1,3/2,by norm_num,by norm_num⟩

omit [CompleteSpace E] in
lemma double_disk_cutoff {u : ℂ → E} (hu : ContDiff ℝ ∞ u) :
    cutoffCurveJet smallDiskBump (largerDiskBump.contDiff.smul hu)=cutoffCurveJet smallDiskBump hu := by
  apply cValue_ext
  intro z
  simp only [cutoffCurveJet_value]
  by_cases hz : smallDiskBump z=0
  · rw [hz,zero_smul,zero_smul]
  · have hr : ‖z‖<(1:ℝ)/2 := by
      have hh : z∈Function.support smallDiskBump := hz
      rw [smallDiskBump.support_eq,Metric.mem_ball,dist_zero_right] at hh
      exact hh
    have hc : largerDiskBump z=1 := largerDiskBump.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall,dist_zero_right]
      change ‖z‖≤(1:ℝ)
      linarith)
    change smallDiskBump z • (largerDiskBump z • u z)=_
    rw [hc,one_smul]

theorem disk_nonlinear_jet_cauchy {L H : ℝ} (hL : 0≤L) (hH : 0≤H) :
    ∃ δ : ℝ,0<δ ∧ ∀ (u : ℕ → ℂ → E) (hu : ∀ i,ContDiff ℝ ∞ (u i))
      (F : ℕ → E → E →L[ℝ] E),
      (∀ i,Continuous (F i)) →(∀ i,F i 0=0) →
      (∀ i x y,‖F i x-F i y‖≤L*‖x-y‖) →(∀ i,u i 0=0) →
      (∀ i z,‖z‖≤2 →‖u i z‖≤δ) →
      (∀ i z,‖z‖≤2 →‖fderiv ℝ (u i) z‖≤H) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →‖u i z-u j z‖≤ε) →
      (∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ v,‖v‖≤δ →‖F i v-F j v‖≤ε) →
      (∀ i z,‖z‖<2 →fderiv ℝ (u i) z Complex.I-Complex.I • fderiv ℝ (u i) z 1=
        F i (u i z) (fderiv ℝ (u i) z 1)) →
      CauchySeq (fun i => cutoffCurveJet smallDiskBump (hu i)) := by
  let c := largerDiskBump
  let B := (boundedCThree_of_compactSupport c.contDiff c.hasCompactSupport).bound
  have hB : 0≤B := (boundedCThree_of_compactSupport c.contDiff c.hasCompactSupport).bound_nonneg
  obtain ⟨d,hd,hcauchy⟩ := cutoff_jet_cauchy (E := E) smallDiskBump (mul_nonneg hL (add_nonneg hH hB))
  let δ := min 1 (d/(L+1))
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hd (by linarith))
  have hδd : L*δ≤d := by
    have hh := (le_div_iff₀ (by linarith : 0<L+1)).mp (min_le_right (1:ℝ) (d/(L+1)))
    nlinarith
  refine ⟨δ,hδ,?_⟩
  intro u hu F hFc hF0 hFL h0 hUb hUd hUc hFuc hcr
  let w : ℕ → ℂ → E := fun i z => c z • u i z
  have hw : ∀ i,ContDiff ℝ ∞ (w i) := fun i => c.contDiff.smul (hu i)
  have hw0 : ∀ i,w i 0=0 := by intro i; simp only [w,h0 i,smul_zero]
  have hwb : ∀ i z,‖w i z‖≤δ := by
    intro i
    exact (smooth_cutoff_local_bounds c (hu i) (by change (3:ℝ)/2≤2; norm_num)
      hδ.le (min_le_left _ _) hH (hUb i) (hUd i)).choose_spec.2.2.1
  have hwd : ∀ i z,‖fderiv ℝ (w i) z‖≤H+B := by
    intro i
    obtain ⟨K,hK,hKe,_,hh⟩ := smooth_cutoff_local_bounds c (hu i) (by change (3:ℝ)/2≤2; norm_num)
      hδ.le (min_le_left _ _) hH (hUb i) (hUd i)
    simpa only [hKe] using hh
  have hwl : ∀ i x y,‖w i x-w i y‖≤(H+B)*dist x y := by
    intro i x y
    rw [dist_eq_norm]
    exact norm_sub_le_of_deriv_bound ((hw i).differentiable (by simp)) (hwd i) x y
  have hwc := cutoff_uniform_cauchy (E := E) c (by change (3:ℝ)/2≤2; norm_num) hUc
  let A : ℕ → ℂ → E →L[ℝ] E := fun i z => F i (w i z)
  have hAb : ∀ i z,‖A i z‖≤d := by
    intro i z
    have hh := hFL i (w i z) 0
    rw [hF0 i,sub_zero,sub_zero] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left (hwb i z) hL).trans hδd)
  have hAl : ∀ i x y,‖A i x-A i y‖≤(L*(H+B))*dist x y := by
    intro i x y
    exact (hFL i _ _).trans ((mul_le_mul_of_nonneg_left (hwl i x y) hL).trans_eq (by ring))
  have hAc := uniform_cauchy_comp_lipschitz hL hFL hwb hwc hFuc
  have heq (i : ℕ) (z : ℂ) (hz : ‖z‖<1) : w i =ᶠ[𝓝 z] u i := by
    have he := c.eventuallyEq_one_of_mem_ball (show z∈Metric.ball (0:ℂ) c.rIn by
      rw [Metric.mem_ball,dist_zero_right]
      change ‖z‖<(1:ℝ)
      exact hz)
    filter_upwards [he] with y hy
    change c y • u i y=u i y
    rw [hy]; exact one_smul ℝ (u i y)
  have hres : ∀ i z,smallDiskBump z≠0 →
      fderiv ℝ (w i) z Complex.I-Complex.I • fderiv ℝ (w i) z 1=A i z (fderiv ℝ (w i) z 1) := by
    intro i z hz
    have hr : ‖z‖<(1:ℝ)/2 := by
      have hh : z∈Function.support smallDiskBump := hz
      rw [smallDiskBump.support_eq,Metric.mem_ball,dist_zero_right] at hh
      exact hh
    have he := heq i z (by linarith)
    change _=F i (w i z) _
    rw [he.fderiv_eq,he.eq_of_nhds]
    exact hcr i z (by linarith)
  have hh := hcauchy w hw A (fun i => (hFc i).comp (hw i).continuous) hw0 hAb hAl
    ⟨δ,H+B,hδ.le,add_nonneg hH hB,hwb,hwl⟩ hwc hAc hres
  have he (i : ℕ) : cutoffCurveJet smallDiskBump (hw i)=cutoffCurveJet smallDiskBump (hu i) := by
    change cutoffCurveJet smallDiskBump (largerDiskBump.contDiff.smul (hu i))=_
    exact double_disk_cutoff (hu i)
  simpa only [he] using hh


end
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}

def compatibleFrame (J : End n) : End n := cayleyP J 1 1

@[simp] lemma compatibleFrame_apply (J : End n) (v : Phase n) :
    compatibleFrame J v = -standardJ n (J v)+v := by
  simp only [compatibleFrame,cayleyP_apply,one_smul,relativeOperator_apply]

lemma compatibleFrame_intertwine {J : End n} (hJ : Compatible J) (v : Phase n) :
    compatibleFrame J (J v) = standardJ n (compatibleFrame J v) := by
  simp only [compatibleFrame_apply,hJ.1,map_neg,map_add,standardJ_sq,neg_neg]
  abel

lemma compatibleFrame_invertible {J : End n} (hJ : Compatible J) :
    (compatibleFrame J).IsInvertible := cayleyP_invertible hJ zero_lt_one zero_le_one

lemma compatibleFrame_standard :
    compatibleFrame (standardJ n) = (2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) := by
  ext v i
  simp only [compatibleFrame_apply,standardJ_sq,neg_neg,Pi.add_apply,
    smul_apply,ContinuousLinearMap.id_apply,Pi.smul_apply]
  exact (two_smul ℝ (v i)).symm

lemma compatibleFrame_smooth {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : D → End n} (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (fun z => compatibleFrame (A z)) := by
  have hI : ContDiff ℝ ∞ (fun _ : D => standardJ n) := contDiff_const
  simpa only [compatibleFrame,cayleyP,one_smul,relativeOperator] using
    ((hI.clm_comp hA).neg.add (contDiff_const (c := ContinuousLinearMap.id ℝ (Phase n))))

lemma compatibleFrame_inverse_smooth {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : D → End n} (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z)) :
    ContDiff ℝ ∞ (fun z => (compatibleFrame (A z)).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (compatibleFrame_invertible (hc z)).contDiffAt_map_inverse.comp z
    (compatibleFrame_smooth hA).contDiffAt

lemma compatibleFrame_inverse_left {J : End n} (hJ : Compatible J) (v : Phase n) :
    (compatibleFrame J).inverse (compatibleFrame J v) = v := by
  obtain ⟨e,he⟩ := compatibleFrame_invertible hJ
  rw [←he]
  simp only [ContinuousLinearMap.inverse_equiv,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

lemma compatibleFrame_inverse_right {J : End n} (hJ : Compatible J) (v : Phase n) :
    compatibleFrame J ((compatibleFrame J).inverse v) = v := by
  obtain ⟨e,he⟩ := compatibleFrame_invertible hJ
  rw [←he]
  simp only [ContinuousLinearMap.inverse_equiv,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

lemma compatibleFrame_inverse_standard :
    (compatibleFrame (standardJ n)).inverse = (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨e,he⟩ := compatibleFrame_invertible (compatible_standardJ n)
  apply (show Function.Injective (compatibleFrame (standardJ n)) by rw [←he]; exact e.injective)
  rw [compatibleFrame_inverse_right (compatible_standardJ n)]
  change v = compatibleFrame (standardJ n) ((1/2:ℝ) • v)
  rw [compatibleFrame_standard]
  simp only [smul_apply,ContinuousLinearMap.id_apply,smul_smul]
  norm_num

variable {K : Set ℂ} (hK : IsCompact K) {A : ℂ → End n}
    (hA : ContDiff ℝ ∞ A) (hc : ∀ z, Compatible (A z))
    (hstd : ∀ z ∉ K, A z = standardJ n)

include hK hstd in
lemma compatibleFrame_compactPerturbation :
    HasCompactSupport (fun z => compatibleFrame (A z) - (2:ℝ) • ContinuousLinearMap.id ℝ (Phase n)) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  apply hz
  change compatibleFrame (A z) - (2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) = 0
  rw [hstd z hzK,compatibleFrame_standard,sub_self]

include hK hstd in
lemma compatibleFrame_inverse_compactPerturbation :
    HasCompactSupport (fun z => (compatibleFrame (A z)).inverse - (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n)) := by
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro z hz
  by_contra hzK
  apply hz
  change (compatibleFrame (A z)).inverse - (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n) = 0
  rw [hstd z hzK,compatibleFrame_inverse_standard,sub_self]

def compatibleFrameJet : COne ℂ (End n) :=
  ofBoundedCThree (boundedCThree_of_compactPerturbation (compatibleFrame_smooth hA) _
    (compatibleFrame_compactPerturbation hK hstd))

def compatibleInverseJet : COne ℂ (End n) :=
  ofBoundedCThree (boundedCThree_of_compactPerturbation (compatibleFrame_inverse_smooth hA hc) _
    (compatibleFrame_inverse_compactPerturbation hK hstd))

@[simp] lemma compatibleFrameJet_value (z : ℂ) :
    cValue (compatibleFrameJet hK hA hstd) z = compatibleFrame (A z) := rfl

@[simp] lemma compatibleInverseJet_value (z : ℂ) :
    cValue (compatibleInverseJet hK hA hc hstd) z = (compatibleFrame (A z)).inverse := rfl

def compatibleMarkedEquiv : markedModel (E := Phase n) K ≃L[ℝ] markedModel (E := Phase n) K :=
  markedCoefficientEquiv hK.isClosed (compatibleFrameJet hK hA hstd)
    (compatibleInverseJet hK hA hc hstd) 2 (1/2)
    (by intro z hz; rw [compatibleFrameJet_value,hstd z hz,compatibleFrame_standard])
    (by intro z hz; rw [compatibleInverseJet_value,hstd z hz,compatibleFrame_inverse_standard])
    (by intro z v; exact compatibleFrame_inverse_left (hc z) v)
    (by intro z v; exact compatibleFrame_inverse_right (hc z) v)

def compatibleResidualEquiv : supportedHolder (E := Phase n) K ≃L[ℝ] supportedHolder (E := Phase n) K :=
  supportedCoefficientEquiv (jetValueCLM _ (compatibleFrameJet hK hA hstd))
    (jetValueCLM _ (compatibleInverseJet hK hA hc hstd))
    (by intro z v; exact compatibleFrame_inverse_left (hc z) v)
    (by intro z v; exact compatibleFrame_inverse_right (hc z) v)



end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
