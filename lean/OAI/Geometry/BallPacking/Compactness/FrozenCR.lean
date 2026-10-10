import Mathlib
import OAI.Geometry.BallPacking.Compactness.JetCauchy

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
variable {n : ℕ}
local instance fcrInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fcrInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def frozenTargetCoefficient (J : Phase n → End n) (x v : Phase n) : End n :=
  let P := compatibleFrame (J x)
  (P.comp (J (x+P.inverse v)-J x)).comp P.inverse

@[simp] lemma frozenTargetCoefficient_zero (J : Phase n → End n) (x : Phase n) :
    frozenTargetCoefficient J x 0=0 := by
  simp only [frozenTargetCoefficient,map_zero,add_zero,sub_self,
    ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp]

lemma frozenTargetCoefficient_continuous {J : Phase n → End n} (hJ : Continuous J) (x : Phase n) :
    Continuous (frozenTargetCoefficient J x) := by
  exact (continuous_const.clm_comp ((hJ.comp (continuous_const.add (compatibleFrame (J x)).inverse.continuous)).sub continuous_const)).clm_comp continuous_const

lemma frozenTargetCoefficient_difference (J : Phase n → End n) (x v w : Phase n) :
    frozenTargetCoefficient J x v-frozenTargetCoefficient J x w=
      ((compatibleFrame (J x)).comp (J (x+(compatibleFrame (J x)).inverse v)-
        J (x+(compatibleFrame (J x)).inverse w))).comp (compatibleFrame (J x)).inverse := by
  apply ContinuousLinearMap.ext
  intro a
  simp only [frozenTargetCoefficient,ContinuousLinearMap.comp_apply,sub_apply,map_sub]
  abel

lemma frozenTargetCoefficient_lipschitz {J : Phase n → End n} {x : Phase n} {L G : ℝ}
    (hL : 0≤L) (hG : 0≤G)
    (hJ : ∀ v w,‖J v-J w‖≤L*‖v-w‖)
    (hP : ‖compatibleFrame (J x)‖≤G) (hPi : ‖(compatibleFrame (J x)).inverse‖≤G) :
    ∀ v w,‖frozenTargetCoefficient J x v-frozenTargetCoefficient J x w‖≤(G^3*L)*‖v-w‖ := by
  intro v w
  let P := compatibleFrame (J x)
  have hp : ∀ z,‖P.inverse z‖≤G*‖z‖ := fun z =>
    (P.inverse.le_opNorm z).trans (mul_le_mul_of_nonneg_right hPi (norm_nonneg _))
  have hj : ‖J (x+P.inverse v)-J (x+P.inverse w)‖≤L*(G*‖v-w‖) := by
    have hh := hJ (x+P.inverse v) (x+P.inverse w)
    rw [add_sub_add_left_eq_sub,←map_sub] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hp _) hL)
  rw [frozenTargetCoefficient_difference]
  have h1 : ‖P.comp (J (x+P.inverse v)-J (x+P.inverse w))‖≤G*(L*(G*‖v-w‖)) :=
    (P.opNorm_comp_le _).trans (mul_le_mul hP hj (norm_nonneg _) hG)
  have hh := (P.comp (J (x+P.inverse v)-J (x+P.inverse w))).opNorm_comp_le P.inverse
  exact hh.trans ((mul_le_mul h1 hPi (norm_nonneg _) (by positivity)).trans_eq (by ring))

def frozenCurve (J : Phase n → End n) (x : Phase n) (u : ℂ → Phase n) (z : ℂ) : Phase n :=
  compatibleFrame (J x) (u z-x)

lemma frozenCurve_smooth {J : Phase n → End n} (x : Phase n) {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (frozenCurve J x u) :=
  (compatibleFrame (J x)).contDiff.comp (hu.sub contDiff_const)

lemma frozenCurve_fderiv {J : Phase n → End n} (x : Phase n) {u : ℂ → Phase n}
    {z : ℂ} (hu : DifferentiableAt ℝ u z) :
    fderiv ℝ (frozenCurve J x u) z=(compatibleFrame (J x)).comp (fderiv ℝ u z) := by
  exact ((compatibleFrame (J x)).hasFDerivAt.comp z (hu.hasFDerivAt.sub_const x)).fderiv

lemma frozenCurve_CR {J : Phase n → End n} {x : Phase n} (hx : Compatible (J x))
    {u : ℂ → Phase n} {z : ℂ} (hu : DifferentiableAt ℝ u z)
    (hcr : fderiv ℝ u z Complex.I=J (u z) (fderiv ℝ u z 1)) :
    fderiv ℝ (frozenCurve J x u) z Complex.I-Complex.I • fderiv ℝ (frozenCurve J x u) z 1=
      frozenTargetCoefficient J x (frozenCurve J x u z) (fderiv ℝ (frozenCurve J x u) z 1) := by
  rw [frozenCurve_fderiv x hu]
  simp only [frozenTargetCoefficient,frozenCurve,ContinuousLinearMap.comp_apply]
  rw [compatibleFrame_inverse_left hx,compatibleFrame_inverse_left hx]
  rw [add_sub_cancel,hcr,sub_apply,map_sub]
  have hh := compatibleFrame_intertwine hx (fderiv ℝ u z 1)
  change compatibleFrame (J x) (J (u z) (fderiv ℝ u z 1))-
      standardJ n (compatibleFrame (J x) (fderiv ℝ u z 1))=_
  rw [←hh]

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Filter
open HolderCompletion
open scoped BoundedContinuousFunction
section
variable {n : ℕ}
local instance hcbInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance hcbInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance hcbInst3 : NormedAddCommGroup (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance hcbInst4 : NormedSpace ℝ (Phase n →L[ℝ] End n) := ContinuousLinearMap.toNormedSpace

lemma lineHomotopy_joint_contDiffAt {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {v : ℝ × Phase n}
    (ht : v.1∈Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun v : ℝ × Phase n => lineHomotopy J v.1 v.2) v :=
  contDiffAt_interpolateJ (hJs.contDiffAt.comp v contDiffAt_snd) contDiffAt_fst (hJ _) ht

lemma lineHomotopy_slice_contDiff {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ContDiff ℝ ∞ (lineHomotopy J t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact contDiffAt_interpolateJ hJs.contDiffAt contDiffAt_const (hJ x) ht

lemma lineHomotopy_partial_deriv {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x)) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Phase n) :
    fderiv ℝ (lineHomotopy J t) x=
      (fderiv ℝ (fun v : ℝ × Phase n => lineHomotopy J v.1 v.2) (t,x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Phase n)) := by
  have hj := (lineHomotopy_joint_contDiffAt hJs hJ (v := (t,x)) ht).differentiableAt (by simp)
  have hg := (hasFDerivAt_const (𝕜 := ℝ) (x := x) t).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
  exact (hj.hasFDerivAt.comp x hg).fderiv

lemma lineHomotopy_eventually_standard {J : Phase n → End n} {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    {x : Phase n} (hx : x∉tsupport (fun x => J x-standardJ n)) :
    lineHomotopy J t =ᶠ[𝓝 x] fun _ => standardJ n := by
  have he := notMem_tsupport_iff_eventuallyEq.mp hx
  filter_upwards [he] with y hy
  have hy' : J y=standardJ n := sub_eq_zero.mp hy
  change interpolateJ (J y) t=standardJ n
  rw [hy']
  exact interpolateJ_standard ht

lemma compatibleFrame_contDiffAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {A : D → End n} {x : D} (hA : ContDiffAt ℝ ∞ A x) :
    ContDiffAt ℝ ∞ (fun z => compatibleFrame (A z)) x := by
  simpa only [compatibleFrame,cayleyP,one_smul,relativeOperator] using
    ((contDiffAt_const.clm_comp hA).neg.add (contDiffAt_const (c := ContinuousLinearMap.id ℝ (Phase n))))

theorem exact_homotopy_target_bounds {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ L G : ℝ,0≤L ∧ 1≤G ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x y,‖lineHomotopy J t x-lineHomotopy J t y‖≤L*‖x-y‖) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,‖compatibleFrame (lineHomotopy J t x)‖≤G) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,‖(compatibleFrame (lineHomotopy J t x)).inverse‖≤G) := by
  let K := (Icc (0:ℝ) 1) ×ˢ tsupport (fun x => J x-standardJ n)
  have hK : IsCompact K := isCompact_Icc.prod hJc
  let A : ℝ × Phase n → End n := fun v => lineHomotopy J v.1 v.2
  let D : ℝ × Phase n → Phase n →L[ℝ] End n := fun v =>
    (fderiv ℝ A v).comp (ContinuousLinearMap.inr ℝ ℝ (Phase n))
  have hDc : ContinuousOn D K := by
    intro v hv
    exact (((lineHomotopy_joint_contDiffAt hJs hJ hv.1).continuousAt_fderiv (by simp)).clm_comp continuousAt_const).continuousWithinAt
  have hPc : ContinuousOn (fun v => compatibleFrame (A v)) K := by
    intro v hv
    exact (compatibleFrame_contDiffAt (lineHomotopy_joint_contDiffAt hJs hJ hv.1)).continuousAt.continuousWithinAt
  have hPic : ContinuousOn (fun v => (compatibleFrame (A v)).inverse) K := by
    intro v hv
    have hp := compatibleFrame_contDiffAt (lineHomotopy_joint_contDiffAt hJs hJ hv.1)
    exact ((compatibleFrame_invertible (lineHomotopy_compatible hJ hv.1 v.2)).contDiffAt_map_inverse.comp v hp).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hDc
  obtain ⟨P,hP⟩ := hK.exists_bound_of_continuousOn hPc
  obtain ⟨Q,hQ⟩ := hK.exists_bound_of_continuousOn hPic
  let L := max B 0
  let G := |P|+|Q|+‖compatibleFrame (standardJ n)‖+‖(compatibleFrame (standardJ n)).inverse‖+1
  have hL : 0≤L := le_max_right B 0
  have hG : 1≤G := by dsimp [G]; linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)]
  have hLd : ∀ t∈Icc (0:ℝ) 1,∀ x,‖fderiv ℝ (lineHomotopy J t) x‖≤L := by
    intro t ht x
    by_cases hx : x∈tsupport (fun x => J x-standardJ n)
    · rw [lineHomotopy_partial_deriv hJs hJ ht x]
      exact (hB (t,x) ⟨ht,hx⟩).trans (le_max_left B 0)
    · rw [(lineHomotopy_eventually_standard ht hx).fderiv_eq]
      simpa only [fderiv_fun_const,Pi.zero_apply,norm_zero] using hL
  refine ⟨L,G,hL,hG,?_,?_,?_⟩
  · intro t ht x y
    exact norm_sub_le_of_deriv_bound ((lineHomotopy_slice_contDiff hJs hJ ht).differentiable (by simp)) (hLd t ht) x y
  · intro t ht x
    by_cases hx : x∈tsupport (fun x => J x-standardJ n)
    · have hh := (hP (t,x) ⟨ht,hx⟩).trans (le_abs_self P)
      exact hh.trans (by dsimp [G]; linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)])
    · rw [(lineHomotopy_eventually_standard ht hx).eq_of_nhds]
      dsimp [G]
      linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)]
  · intro t ht x
    by_cases hx : x∈tsupport (fun x => J x-standardJ n)
    · have hh := (hQ (t,x) ⟨ht,hx⟩).trans (le_abs_self Q)
      exact hh.trans (by dsimp [G]; linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)])
    · rw [(lineHomotopy_eventually_standard ht hx).eq_of_nhds]
      dsimp [G]
      linarith [abs_nonneg P,abs_nonneg Q,norm_nonneg (compatibleFrame (standardJ n)),norm_nonneg ((compatibleFrame (standardJ n)).inverse)]

end
section

variable {n : ℕ}
local instance fhcInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance fhcInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

lemma frozenHomotopy_joint_contDiffAt {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {v : (ℝ × Phase n) × Phase n} (ht : v.1.1∈Icc (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun w : (ℝ × Phase n) × Phase n =>
      frozenTargetCoefficient (lineHomotopy J w.1.1) w.1.2 w.2) v := by
  have htfun : ContDiffAt ℝ ∞ (fun w : (ℝ × Phase n) × Phase n => w.1.1) v :=
    contDiffAt_fst.comp v contDiffAt_fst
  have hxfun : ContDiffAt ℝ ∞ (fun w : (ℝ × Phase n) × Phase n => w.1.2) v :=
    contDiffAt_snd.comp v contDiffAt_fst
  let A : (ℝ × Phase n) × Phase n → End n := fun w => lineHomotopy J w.1.1 w.1.2
  have hA : ContDiffAt ℝ ∞ A v :=
    contDiffAt_interpolateJ (hJs.contDiffAt.comp v hxfun) htfun (hJ _) ht
  let P : (ℝ × Phase n) × Phase n → End n := fun w => compatibleFrame (A w)
  have hP : ContDiffAt ℝ ∞ P v := compatibleFrame_contDiffAt hA
  have hi : ContDiffAt ℝ ∞ (fun T : End n => T.inverse) (P v) :=
    (compatibleFrame_invertible (lineHomotopy_compatible hJ ht v.1.2)).contDiffAt_map_inverse
  have hPi : ContDiffAt ℝ ∞ (fun w => (P w).inverse) v := hi.comp v hP
  have harg : ContDiffAt ℝ ∞ (fun w => w.1.2+(P w).inverse w.2) v :=
    hxfun.add (hPi.clm_apply contDiffAt_snd)
  have hB : ContDiffAt ℝ ∞ (fun w => lineHomotopy J w.1.1 (w.1.2+(P w).inverse w.2)) v :=
    contDiffAt_interpolateJ (hJs.contDiffAt.comp v harg) htfun (hJ _) ht
  exact (hP.clm_comp (hB.sub hA)).clm_comp hPi

lemma frozenHomotopy_tendstoUniformlyOn {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1) {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {x : ℕ → Phase n} {y : Phase n} (hx : Tendsto x atTop (𝓝 y))
    {K : Set (Phase n)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun i => frozenTargetCoefficient (lineHomotopy J (t i)) (x i))
      (frozenTargetCoefficient (lineHomotopy J s) y) atTop K := by
  have hsI : s∈Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hs (Eventually.of_forall ht)
  let U : Set (ℝ × Phase n) := (Icc (0:ℝ) 1) ×ˢ insert y (range x)
  have hU : IsCompact U := isCompact_Icc.prod hx.isCompact_insert_range
  have hc : ContinuousOn (fun w : (ℝ × Phase n) × Phase n =>
      frozenTargetCoefficient (lineHomotopy J w.1.1) w.1.2 w.2) (U ×ˢ K) := by
    intro w hw
    exact (frozenHomotopy_joint_contDiffAt hJs hJ hw.1.1).continuousAt.continuousWithinAt
  have huc := (hU.prod hK).uniformContinuousOn_of_continuous hc
  have hlim := UniformContinuousOn.tendstoUniformlyOn
    (F := fun a : ℝ × Phase n => frozenTargetCoefficient (lineHomotopy J a.1) a.2) huc (show (s,y)∈U from ⟨hsI,mem_insert _ _⟩)
  have hp : Tendsto (fun i => (t i,x i)) atTop (𝓝[U] (s,y)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs.prodMk_nhds hx,Eventually.of_forall (fun i => ⟨ht i,mem_insert_of_mem _ ⟨i,rfl⟩⟩)⟩
  intro W hW
  exact hp (hlim W hW)

lemma exact_frame_tendsto {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    {t : ℕ → ℝ} (ht : ∀ i,t i∈Icc (0:ℝ) 1) {s : ℝ} (hs : Tendsto t atTop (𝓝 s))
    {x : ℕ → Phase n} {y : Phase n} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun i => compatibleFrame (lineHomotopy J (t i) (x i))) atTop
      (𝓝 (compatibleFrame (lineHomotopy J s y))) ∧
    Tendsto (fun i => (compatibleFrame (lineHomotopy J (t i) (x i))).inverse) atTop
      (𝓝 (compatibleFrame (lineHomotopy J s y)).inverse) := by
  have hsI : s∈Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hs (Eventually.of_forall ht)
  have hP := compatibleFrame_contDiffAt (lineHomotopy_joint_contDiffAt hJs hJ (v := (s,y)) hsI)
  have hp := hP.continuousAt.tendsto.comp (hs.prodMk_nhds hx)
  refine ⟨hp,?_⟩
  have hi : ContDiffAt ℝ ∞ (fun T : End n => T.inverse) (compatibleFrame (lineHomotopy J s y)) :=
    (compatibleFrame_invertible (lineHomotopy_compatible hJ hsI y)).contDiffAt_map_inverse
  exact hi.continuousAt.tendsto.comp hp

end

lemma weighted_gradient_selection {X : Type*} [MetricSpace X] [ProperSpace X]
    {f : X → ℝ} (hf : Continuous f) (hn : ∀ x,0≤f x)
    (x : X) {R : ℝ} (hR : 0<R) (hx : 0<f x) :
    ∃ y : X,∃ r : ℝ,0<r ∧ dist y x+r≤R ∧ 0<f y ∧
      R*f x≤2*r*f y ∧ ∀ z,dist z y≤r → f z≤2*f y := by
  let g : X → ℝ := fun y => (R-dist y x)*f y
  have hg : Continuous g := (continuous_const.sub (continuous_id.dist continuous_const)).mul hf
  obtain ⟨y,hy,hmax⟩ := (isCompact_closedBall x R).exists_isMaxOn
    ⟨x,Metric.mem_closedBall_self hR.le⟩ hg.continuousOn
  have hm : R*f x≤(R-dist y x)*f y := by
    have hh := hmax (Metric.mem_closedBall_self hR.le)
    change (R-dist x x)*f x≤(R-dist y x)*f y at hh
    simpa only [dist_self,sub_zero] using hh
  have hdy : dist y x<R := by
    by_contra! h
    have hnz : (R-dist y x)*f y≤0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (hn y)
    have hp := mul_pos hR hx
    linarith
  have hfy : 0<f y := by
    by_contra! h
    have hh : f y=0 := le_antisymm h (hn y)
    rw [hh,mul_zero] at hm
    exact (not_le_of_gt (mul_pos hR hx)) hm
  let r : ℝ := (R-dist y x)/2
  have hr : 0<r := by dsimp [r]; linarith
  have hrr : dist y x+r≤R := by dsimp [r]; linarith
  refine ⟨y,r,hr,hrr,hfy,by dsimp [r]; nlinarith [hm],?_⟩
  intro z hz
  have hzx : dist z x≤R := (dist_triangle z y x).trans (by linarith)
  have hzg := hmax (show z∈Metric.closedBall x R from hzx)
  change (R-dist z x)*f z≤(R-dist y x)*f y at hzg
  have hcoef : r≤R-dist z x := by
    have hh := dist_triangle z y x
    dsimp [r] at *
    linarith
  have hh := mul_le_mul_of_nonneg_right hcoef (hn z)
  have he : R-dist y x=2*r := by dsimp [r]; ring
  rw [he] at hzg
  have hmul : r*f z≤r*(2*f y) := (hh.trans hzg).trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ hr).mp hmul

variable {n : ℕ}
local instance ecgInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance ecgInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

def rescaledCurve (u : ℂ → Phase n) (y : ℂ) (r : ℝ) (z : ℂ) : Phase n := u (y+r • z)

lemma rescaledCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (y : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (rescaledCurve u y r) := hu.comp (contDiff_const.add (contDiff_id.const_smul r))

lemma rescaledCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (y : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaledCurve u y r) z=r • fderiv ℝ u (y+r • z) := by
  have hh := (hu.differentiable (by simp) (y+r • z)).hasFDerivAt.comp z
    (((ContinuousLinearMap.id ℝ ℂ).hasFDerivAt.const_smul r).const_add y)
  have he : (fderiv ℝ u (y+r • z)).comp (r • ContinuousLinearMap.id ℝ ℂ)=
      r • fderiv ℝ u (y+r • z) := by ext h; simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul]
  rw [he] at hh
  exact hh.fderiv

lemma rescaledCurve_CR {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hcr : ∀ z,PseudoHolomorphicAt J u z) (y : ℂ) (r : ℝ) (z : ℂ) :
    fderiv ℝ (rescaledCurve u y r) z Complex.I=
      J (rescaledCurve u y r z) (fderiv ℝ (rescaledCurve u y r) z 1) := by
  rw [rescaledCurve_fderiv hu y r z]
  simp only [smul_apply,map_smul]
  have hh := (hcr (y+r • z)).2 1
  simp only [mul_one] at hh
  exact congrArg (fun v => r • v) hh

lemma rescaledCurve_source_dist (y z : ℂ) {r : ℝ} (hr : 0≤r) : dist (y+r • z) y=r*‖z‖ := by
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]

theorem equicontinuous_CR_derivative_bound {ι : Type*} (J : ι → Phase n → End n)
    (u : ι → ℂ → Phase n) (hu : ∀ i,ContDiff ℝ ∞ (u i))
    (hJc : ∀ i,Continuous (J i)) (hJ : ∀ i x,Compatible (J i x))
    (hcr : ∀ i z,PseudoHolomorphicAt (J i) (u i) z)
    {L G : ℝ} (hL : 0≤L) (hG : 1≤G)
    (hJL : ∀ i x y,‖J i x-J i y‖≤L*‖x-y‖)
    (hP : ∀ i x,‖compatibleFrame (J i x)‖≤G)
    (hPi : ∀ i x,‖(compatibleFrame (J i x)).inverse‖≤G)
    (hm : ∀ ε : ℝ,0<ε →∃ δ : ℝ,0<δ ∧ ∀ i x y,dist x y<δ →dist (u i x) (u i y)<ε) :
    ∃ M : ℝ,0<M ∧ ∀ i z,‖fderiv ℝ (u i) z‖≤M := by
  have hG0 : 0<G := lt_of_lt_of_le zero_lt_one hG
  obtain ⟨e,he,hell⟩ := local_nonlinear_gradient_small (E := Phase n)
    (by positivity : 0≤G^3*L) (by positivity : 0≤G*2) (div_pos zero_lt_one hG0)
  obtain ⟨d,hd,hmod⟩ := hm (e/G) (div_pos he hG0)
  let M := max 4 (4/d)+1
  have hM : 0<M := by dsimp [M]; linarith [le_max_left (4:ℝ) (4/d)]
  refine ⟨M,hM,?_⟩
  intro i x
  by_contra! hgt
  let f : ℂ → ℝ := fun z => ‖fderiv ℝ (u i) z‖
  have hfx : 0<f x := hM.trans hgt
  have hfc : Continuous f := ((hu i).continuous_fderiv (by simp)).norm
  obtain ⟨y,s,hs,hsy,hfy,hweight,hsel⟩ := weighted_gradient_selection hfc (fun _ => norm_nonneg _) x zero_lt_one hfx
  have hs1 : s≤1 := by linarith [dist_nonneg (x := y) (y := x)]
  have hfx4 : 4<f x := by have hh := le_max_left (4:ℝ) (4/d); dsimp [M] at hgt; linarith
  have hfxd : 4/d<f x := by have hh := le_max_right (4:ℝ) (4/d); dsimp [M] at hgt; linarith
  have hfxfy : f x≤2*f y := by
    have hh := mul_le_mul_of_nonneg_right hs1 hfy.le
    nlinarith only [hweight,hh]
  have hradius : 2/f y<s := by
    apply (div_lt_iff₀ hfy).mpr
    nlinarith only [hweight,hfx4]
  have hor : 2/f y<d := by
    have hh := (div_lt_iff₀ hd).mp hfxd
    apply (div_lt_iff₀ hfy).mpr
    nlinarith [mul_le_mul_of_nonneg_right hfxfy hd.le]
  let r : ℝ := (f y)⁻¹
  have hr : 0<r := inv_pos.mpr hfy
  let v := rescaledCurve (u i) y r
  have hv : ContDiff ℝ ∞ v := rescaledCurve_smooth (hu i) y r
  have hv0 : v 0=u i y := by simp only [v,rescaledCurve,smul_zero,add_zero]
  have hdist : ∀ z,‖z‖≤2 →dist (y+r • z) y≤2/f y := by
    intro z hz
    rw [rescaledCurve_source_dist y z hr.le]
    have hh := mul_le_mul_of_nonneg_left hz hr.le
    simpa only [r,mul_comm,div_eq_mul_inv] using hh
  have hvd : ∀ z,‖z‖≤2 →‖fderiv ℝ v z‖≤2 := by
    intro z hz
    rw [rescaledCurve_fderiv (hu i),norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le]
    have hh := hsel (y+r • z) ((hdist z hz).trans hradius.le)
    have hm := mul_le_mul_of_nonneg_left hh hr.le
    have hid : r*(2*f y)=2 := by dsimp [r]; field_simp
    exact hm.trans_eq hid
  have hvd0 : ‖fderiv ℝ v 0‖=1 := by
    rw [rescaledCurve_fderiv (hu i),smul_zero,add_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr.le]
    change (f y)⁻¹*f y=1
    exact inv_mul_cancel₀ hfy.ne'
  let a := u i y
  let w := frozenCurve (J i) a v
  have hw : ContDiff ℝ ∞ w := frozenCurve_smooth a hv
  have hw0 : w 0=0 := by simp only [w,frozenCurve,hv0,a,sub_self,map_zero]
  have hwb : ∀ z,‖z‖≤2 →‖w z‖≤e := by
    intro z hz
    have ho := hmod i (y+r • z) y ((hdist z hz).trans_lt hor)
    rw [dist_eq_norm] at ho
    have ht : G*‖v z-a‖<e := by
      have hh := (lt_div_iff₀ hG0).mp ho
      simpa only [v,rescaledCurve,a,mul_comm] using hh
    exact ((compatibleFrame (J i a)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hP i a) (norm_nonneg _)).trans ht.le)
  have hwD : ∀ z,‖z‖≤2 →‖fderiv ℝ w z‖≤G*2 := by
    intro z hz
    rw [frozenCurve_fderiv a (hv.differentiable (by simp) z)]
    exact ((compatibleFrame (J i a)).opNorm_comp_le _).trans
      (mul_le_mul (hP i a) (hvd z hz) (norm_nonneg _) hG0.le)
  have hwcr : ∀ z,‖z‖<2 → fderiv ℝ w z Complex.I-Complex.I • fderiv ℝ w z 1=
      frozenTargetCoefficient (J i) a (w z) (fderiv ℝ w z 1) := by
    intro z _
    exact frozenCurve_CR (hJ i a) (hv.differentiable (by simp) z)
      (rescaledCurve_CR (hu i) (hcr i) y r z)
  have hh := hell (frozenTargetCoefficient (J i) a) (frozenTargetCoefficient_continuous (hJc i) a)
    (frozenTargetCoefficient_zero _ _) (frozenTargetCoefficient_lipschitz hL hG0.le (hJL i) (hP i a) (hPi i a))
    w hw hw0 hwb hwD hwcr
  have heD : ((compatibleFrame (J i a)).inverse).comp (fderiv ℝ w 0)=fderiv ℝ v 0 := by
    rw [frozenCurve_fderiv a (hv.differentiable (by simp) 0)]
    apply ContinuousLinearMap.ext
    intro z
    exact compatibleFrame_inverse_left (hJ i a) _
  have hnorm := ((compatibleFrame (J i a)).inverse).opNorm_comp_le (fderiv ℝ w 0)
  rw [heD,hvd0] at hnorm
  have hc : 1≤G*‖fderiv ℝ w 0‖ := hnorm.trans
    (mul_le_mul_of_nonneg_right (hPi i a) (norm_nonneg _))
  have hlt := (lt_div_iff₀ hG0).mp hh
  nlinarith

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped Topology ContDiff
open Set Filter
variable {X E F : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MetricSpace X] [NormedSpace ℝ E] in
lemma uniform_values_cauchy_on {u : ℕ → X → E} {v : X → E} {K : Set X}
    (hu : TendstoUniformlyOn u v atTop K) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x∈K,‖u i x-u j x‖≤ε := by
  have hh := (tendstoUniformlyOn_iff_restrict.mp hu)
  have hc := uniform_cauchy_of_tendstoUniformly hh
  intro ε hε
  obtain ⟨N,hN⟩ := hc ε hε
  exact ⟨N,fun i hi j hj x hx => hN i hi j hj ⟨x,hx⟩⟩

omit [MetricSpace X] in
lemma uniform_clm_cauchy_on {P : ℕ → E →L[ℝ] F} {u : ℕ → X → E} {K : Set X}
    {G M : ℝ} (hG : 0≤G) (hM : 0≤M)
    (hP : ∀ i,‖P i‖≤G) (hu : ∀ i,∀ x∈K,‖u i x‖≤M)
    (hPc : CauchySeq P)
    (huc : ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x∈K,‖u i x-u j x‖≤ε) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ x∈K,‖P i (u i x)-P j (u j x)‖≤ε := by
  intro ε hε
  have hh : 0<G+M+1 := by linarith
  let d := ε/(G+M+1)
  have hd : 0<d := div_pos hε hh
  obtain ⟨N,hN⟩ := huc d hd
  obtain ⟨Q,hQ⟩ := Metric.cauchySeq_iff.mp hPc d hd
  refine ⟨max N Q,fun i hi j hj x hx => ?_⟩
  have h1 := hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) x hx
  have h2 := hQ i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj)
  rw [dist_eq_norm] at h2
  have hbound := clm_pair_difference (P i) (P j) (u i x) (u j x)
  have hA := mul_le_mul (hP i) h1 (norm_nonneg _) hG
  have hB := mul_le_mul h2.le (hu j x hx) (norm_nonneg _) hd.le
  have he : G*d+d*M≤ε := by
    have hid : (G+M+1)*d=ε := mul_div_cancel₀ ε (ne_of_gt hh)
    nlinarith
  exact hbound.trans ((add_le_add hA hB).trans he)

variable {n : ℕ}
lemma centered_rescaled_cauchy {u : ℕ → ℂ → Phase n} {v : ℂ → Phase n}
    (hu : ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn u v atTop K) (c : ℂ) (r : ℝ) :
    ∀ ε : ℝ,0<ε →∃ N : ℕ,∀ i≥N,∀ j≥N,∀ z,‖z‖≤2 →
      ‖(rescaledCurve (u i) c r z-u i c)-(rescaledCurve (u j) c r z-u j c)‖≤ε := by
  let K := (fun z : ℂ => c+r • z) '' Metric.closedBall (0:ℂ) 2
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) 2).image (continuous_const.add (continuous_id.const_smul r))
  have hval := uniform_values_cauchy_on (hu K hK)
  intro ε hε
  obtain ⟨N,hN⟩ := hval (ε/2) (half_pos hε)
  refine ⟨N,fun i hi j hj z hz => ?_⟩
  have hzK : c+r • z∈K := ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,rfl⟩
  have hcK : c∈K := ⟨0,by simp,by simp⟩
  have h1 := hN i hi j hj (c+r • z) hzK
  have h2 := hN i hi j hj c hcK
  have he : (rescaledCurve (u i) c r z-u i c)-(rescaledCurve (u j) c r z-u j c)=
      (u i (c+r • z)-u j (c+r • z))-(u i c-u j c) := by dsimp [rescaledCurve]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
