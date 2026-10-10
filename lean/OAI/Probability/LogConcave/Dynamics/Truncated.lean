import Mathlib
import OAI.Probability.LogConcave.Dynamics.TriangularEquiv
import OAI.Probability.LogConcave.Sampling.MeasureSmoothLipschitz

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def truncated (f : E → E) (n : ℕ) (x : E) : E := PoincareCutoff.cutoff n x • f x

lemma truncated_smooth {f : E → E} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ContDiff ℝ 1 (truncated f n) := (PoincareCutoff.cutoff_smooth n).smul hf

lemma truncated_lipschitz {f : E → E} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ∃ L : ℝ≥0,LipschitzWith L (truncated f n) :=
  ContDiff.lipschitzWith_of_hasCompactSupport
    ((PoincareCutoff.cutoff_compact n).smul_right (f':=f)) (truncated_smooth hf n) (by norm_num)

lemma cutoff_eq_one {n : ℕ} {x : E} (hx : ‖x‖≤(n:ℝ)+1) :
    PoincareCutoff.cutoff n x=1 := by
  apply (PoincareCutoff.bump (E:=E)).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  change ‖((n:ℝ)+1)⁻¹ • x‖≤1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact (inv_mul_le_iff₀ (by positivity : 0<(n:ℝ)+1)).mpr (by simpa using hx)

lemma truncated_eq {f : E → E} {n : ℕ} {x : E} (hx : ‖x‖≤(n:ℝ)+1) :
    truncated f n x=f x := by simp [truncated,cutoff_eq_one hx]

lemma truncated_growth {f : E → E} {K B : ℝ}
    (hg : ∀x,‖f x‖≤K*‖x‖+B) (n : ℕ) (x : E) :
    ‖truncated f n x‖≤K*‖x‖+B := by
  rw [truncated,norm_smul,Real.norm_eq_abs,abs_of_nonneg (PoincareCutoff.cutoff_nonneg n x)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (PoincareCutoff.cutoff_le_one n x)).trans (hg x)

theorem exists_curve {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    ∃α : ℝ → E,Continuous α ∧ α a=x ∧
      (∀t∈Icc a b,HasDerivWithinAt α (f (α t)) (Icc a b) t) ∧
      ∀t∈Icc a b,‖α t‖≤gronwallBound ‖x‖ K B (t-a) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (gronwallBound ‖x‖ K B (b-a))
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  have hc : Continuous (uncurry (fun (_ : ℝ) => truncated f n)) :=
    (truncated_smooth hf n).continuous.comp continuous_snd
  obtain ⟨α,hα,hα0,hαd⟩ := GlobalODE.exists_curve (f:=fun _ => truncated f n)
    (⟨a,le_rfl,hab⟩ : Icc a b) hc (fun _ _ => hL) x
  have hb : ∀t∈Icc a b,‖α t‖≤gronwallBound ‖x‖ K B (t-a) :=
    norm_le_gronwallBound_of_norm_deriv_right_le hα.continuousOn
      (GlobalODE.right_deriv hαd) (by rw [hα0])
      (fun t _ => truncated_growth hg n (α t))
  have he (t : ℝ) (ht : t∈Icc a b) : truncated f n (α t)=f (α t) := by
    apply truncated_eq
    exact (hb t ht).trans ((gronwallBound_mono (norm_nonneg x) hB hK
      (sub_le_sub_right ht.2 a)).trans (by linarith))
  exact ⟨α,hα,hα0,fun t ht => (he t ht) ▸ hαd t ht,hb⟩

theorem unique {f : E → E} (hf : ContDiff ℝ 1 f) {a b : ℝ} {α β : ℝ → E}
    (hα : ContinuousOn α (Icc a b)) (hβ : ContinuousOn β (Icc a b))
    (hdα : ∀t∈Icc a b,HasDerivWithinAt α (f (α t)) (Icc a b) t)
    (hdβ : ∀t∈Icc a b,HasDerivWithinAt β (f (β t)) (Icc a b) t)
    (h0 : α a=β a) : Set.EqOn α β (Icc a b) := by
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  obtain ⟨L,hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num : (1:WithTop ℕ∞)≠0)
    (convex_closedBall (0:E) (max A B)) (isCompact_closedBall (0:E) (max A B))
  intro t ht
  have hh := dist_le_of_trajectories_ODE_of_mem (v:=fun (_ : ℝ) => f)
    (s:=fun _ => Metric.closedBall (0:E) (max A B))
    (fun _ _ => hL) hα (GlobalODE.right_deriv hdα)
    (fun u hu => by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (hA u ⟨hu.1,hu.2.le⟩).trans (le_max_left A B))
    hβ (GlobalODE.right_deriv hdβ)
    (fun u hu => by simpa only [Metric.mem_closedBall,dist_zero_right] using
      (hB u ⟨hu.1,hu.2.le⟩).trans (le_max_right A B)) (show dist (α a) (β a)≤0 by simp [h0]) t ht
  simpa only [h0,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma growth_from_right {a b K B R : ℝ} {α β : ℝ → E}
    (hc : ContinuousOn α (Icc a b))
    (hd : ∀t∈Icc a b,HasDerivWithinAt α (β t) (Icc a b) t)
    (hb : ‖α b‖≤R) (hg : ∀t∈Icc a b,‖β t‖≤K*‖α t‖+B)
    (t : ℝ) (ht : t∈Icc a b) : ‖α t‖≤gronwallBound R K B (b-t) := by
  let q : ℝ → ℝ := fun u => a+b-u
  have hq (u : ℝ) (hu : u∈Icc a b) : q u∈Icc a b := by
    constructor <;> dsimp [q] <;> linarith [hu.1,hu.2]
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hαc : ContinuousOn (α ∘ q) (Icc a b) := hc.comp hqc.continuousOn hq
  have hαd (u : ℝ) (hu : u∈Icc a b) :
      HasDerivWithinAt (α ∘ q) (-β (q u)) (Icc a b) u := by
    have hqd : HasDerivWithinAt q (-1) (Icc a b) u := by
      convert! ((hasDerivWithinAt_const u (Icc a b) (a+b)).sub
        (hasDerivWithinAt_id u (Icc a b))) using 1
      simp
    simpa only [neg_one_smul] using (hd (q u) (hq u hu)).scomp u hqd hq
  have h0 : ‖(α ∘ q) a‖≤R := by simpa [q] using hb
  have hβb (u : ℝ) (_hu : u∈Ico a b) :
      ‖-β (q u)‖≤K*‖(α ∘ q) u‖+B := by
    simpa only [norm_neg,comp_apply] using hg (q u) (hq u ⟨_hu.1,_hu.2.le⟩)
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hαc
    (GlobalODE.right_deriv (f := fun u (_ : E) => -β (q u)) hαd) h0 hβb (q t) (hq t ht)
  simpa only [comp_apply,q,show a+b-(a+b-t)=t by ring,show a+b-t-a=b-t by ring] using hh

lemma gronwallBound_initial_mono {R S K B t : ℝ} (h : R≤S) :
    gronwallBound R K B t≤gronwallBound S K B t := by
  unfold gronwallBound
  split_ifs <;> gcongr

variable [FiniteDimensional ℝ E]

def flow {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) : ℝ → E :=
  (exists_curve hf hK hB hg hab x).choose
lemma flow_continuous {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    Continuous (flow hf hK hB hg hab x) := (exists_curve hf hK hB hg hab x).choose_spec.1
lemma flow_initial {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    flow hf hK hB hg hab x a=x := (exists_curve hf hK hB hg hab x).choose_spec.2.1
lemma flow_deriv {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    ∀t∈Icc a b,HasDerivWithinAt (flow hf hK hB hg hab x)
      (f (flow hf hK hB hg hab x t)) (Icc a b) t :=
  (exists_curve hf hK hB hg hab x).choose_spec.2.2.1
lemma flow_growth {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (x : E) :
    ∀t∈Icc a b,‖flow hf hK hB hg hab x t‖≤gronwallBound ‖x‖ K B (t-a) :=
  (exists_curve hf hK hB hg hab x).choose_spec.2.2.2
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma truncated_continuous {f : E → E} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    Continuous (uncurry (fun (_ : ℝ) => truncated f n)) :=
  (truncated_smooth hf n).continuous.comp continuous_snd

lemma truncated_flow_growth {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b) (n : ℕ)
    {L : ℝ≥0} (hL : LipschitzWith L (truncated f n)) (y : E) :
    ∀t∈Icc a b,‖GlobalODE.flow (fun _ _ => hL)
      (truncated_continuous hf n) ⟨a,le_rfl,hab⟩ y t‖≤
        gronwallBound ‖y‖ K B (t-a) := by
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    (GlobalODE.flow_continuous _ _ _ _).continuousOn
    (GlobalODE.right_deriv (GlobalODE.flow_deriv _ _ _ _))
    (by rw [GlobalODE.flow_initial])
  exact fun _ _ => truncated_growth hg n _

lemma eq_truncated_flow {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b R : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (n : ℕ) {L : ℝ≥0} (hL : LipschitzWith L (truncated f n))
    (hn : gronwallBound R K B (b-a)≤(n:ℝ)+1) {y : E} (hy : ‖y‖≤R) :
    EqOn (flow hf hK hB hg hab y)
      (GlobalODE.flow (fun _ _ => hL) (truncated_continuous hf n)
        ⟨a,le_rfl,hab⟩ y) (Icc a b) := by
  let α := GlobalODE.flow (fun _ _ => hL)
    (truncated_continuous hf n) (⟨a,le_rfl,hab⟩ : Icc a b) y
  have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivWithinAt α (f (α t)) (Icc a b) t := by
    have hb := truncated_flow_growth hf hg hab n hL y t ht
    have hb' : ‖α t‖≤(n:ℝ)+1 := hb.trans ((gronwallBound_initial_mono hy).trans
      ((gronwallBound_mono ((norm_nonneg y).trans hy) hB hK (sub_le_sub_right ht.2 a)).trans hn))
    have he := truncated_eq (f:=f) hb'
    exact he ▸ GlobalODE.flow_deriv (fun _ _ => hL) _ _ y t ht
  apply unique hf (flow_continuous hf hK hB hg hab y).continuousOn
    (GlobalODE.flow_continuous _ _ _ _).continuousOn (flow_deriv hf hK hB hg hab y) hd
  rw [flow_initial,GlobalODE.flow_initial]

lemma flow_continuous_initial {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (t : ℝ) (ht : t∈Icc a b) : Continuous (fun y => flow hf hK hB hg hab y t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨n,hn⟩ := exists_nat_gt (gronwallBound (‖x‖+1) K B (b-a))
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  have hh := (GlobalODE.flow_lipschitz (fun _ _ => hL)
    (truncated_continuous hf n) ⟨a,le_rfl,hab⟩ ⟨t,ht⟩).continuous.continuousAt (x:=x)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1)] with y hy
  apply (eq_truncated_flow hf hK hB hg hab n hL (by linarith) ?_ ht)
  calc ‖y‖≤‖x‖+dist y x := norm_le_norm_add_const_of_dist_le le_rfl
       _≤‖x‖+1 := by gcongr; exact (Metric.mem_ball.mp hy).le

lemma backwardTest_vanish {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b R : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a≤b)
    (hR : 0≤R) {φ : E → ℝ} (hφ : ∀x,R<‖x‖ → φ x=0)
    (n : ℕ) {L : ℝ≥0} (hL : LipschitzWith L (truncated f n)) (t : ℝ) (y : E)
    (hy : gronwallBound R K B (b-a)<‖y‖) :
    GlobalODE.backwardTest (f:=fun (_ : ℝ) => truncated f n) hab
      (truncated_continuous hf n) (fun _ _ => hL)
      ⟨b,hab,le_rfl⟩ φ (t,y)=0 := by
  rw [GlobalODE.backwardTest_eq]
  apply hφ
  by_contra! h
  let s := projIcc a b hab t
  let α := GlobalODE.flow (fun _ _ => hL)
    (truncated_continuous hf n) s y
  have hh := growth_from_right (GlobalODE.flow_continuous _ _ _ _).continuousOn
    (GlobalODE.flow_deriv (fun _ _ => hL) _ s y) h
    (fun u _ => truncated_growth hg n (α u)) s s.2
  rw [GlobalODE.flow_initial] at hh
  have hm := gronwallBound_mono hR hB hK (sub_le_sub_left s.2.1 b)
  exact (not_lt_of_ge (hh.trans hm)) hy
end LogConcaveSampling.LinearGrowthODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stationary_integral_of_backward_flux {f : E → E} (hf : ContDiff ℝ 1 f)
    {K : ℝ≥0} (hL : LipschitzWith K f) {μ : Measure E} [IsFiniteMeasure μ]
    (hfi : Integrable (fun x => ‖f x‖) μ)
    {a b : ℝ} (hab : a<b) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hφL : LipschitzWith L φ) {B : ℝ} (hφB : ∀x,‖φ x‖≤B)
    (hflux : ∀t : ℝ,(∫y,(fderiv ℝ (fun z =>
      backwardTest (f:=fun (_ : ℝ) => f) hab.le (hf.continuous.comp continuous_snd) (fun _ _ => hL)
        ⟨b,hab.le,le_rfl⟩ φ (t,z)) y) (f y) ∂μ)=0) :
    (∫y,φ (flow (fun _ _ => hL) (hf.continuous.comp continuous_snd)
      ⟨a,le_rfl,hab.le⟩ y b) ∂μ)=∫y,φ y ∂μ := by
  let hc : Continuous (uncurry (fun (_ : ℝ) => f)) := hf.continuous.comp continuous_snd
  let hD : Continuous (uncurry (fun (_ : ℝ) => fderiv ℝ f)) :=
    (hf.continuous_fderiv (by norm_num)).comp continuous_snd
  let hd : ∀ (u : ℝ) (z : E),HasFDerivAt f (fderiv ℝ f z) z :=
    fun _ z => (hf.differentiable (by norm_num) z).hasFDerivAt
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := backwardTest hab.le hc (fun _ _ => hL) T φ
  let S := fun t => fderiv ℝ (fun y => ψ (t,y))
  let C : ℝ := (L:ℝ)*Real.exp ((K:ℝ)*(b-a))
  have hC : 0≤C := by dsimp [C]; positivity
  have hψ : Continuous ψ := backwardTest_continuous hab.le hc (fun _ _ => hL) T hφ.continuous
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun y => ψ (t,y)) := by
    have he : (fun y => ψ (t,y))=φ ∘ (fun y =>
        flow (fun _ _ => hL) hc (projIcc a b hab.le t) y T) := by
      funext y
      exact backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,y)
    rw [he]
    exact hφ.comp (flow_contDiff_one hab.le hc (fun _ _ => hL) hD hd _ T)
  have hψL (t : ℝ) := backwardTest_lipschitz hab.le hc (fun _ _ => hL) T hφL t
  have hψB (t : ℝ) (y : E) : ‖ψ (t,y)‖≤B := hφB _
  have hSb (t : ℝ) (y : E) : ‖S t y‖≤C := norm_fderiv_le_of_lipschitz ℝ (hψL t)
  have him (t : ℝ) : Integrable (fun y => ψ (t,y)) μ :=
    (integrable_const B).mono' (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall (hψB t))
  have hdm (t : ℝ) : Measurable (fun y => -(S t y (f y))) :=
    ((continuous_fst.clm_apply continuous_snd).measurable.comp
      ((measurable_fderiv ℝ (fun y => ψ (t,y))).prodMk hf.continuous.measurable)).neg
  have hdb (t : ℝ) (y : E) : ‖-(S t y (f y))‖≤C*‖f y‖ := by
    rw [norm_neg]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hSb t y) (norm_nonneg _))
  have hpd (t : ℝ) (ht : t∈Ioo a b) (y : E) :
      HasDerivAt (fun t => ψ (t,y)) (-(S t y (f y))) t := by
    have hh := backwardTest_chain hab.le hc (fun _ _ => hL) hD hd T
      (hφ.differentiable (by norm_num)) ht (hasDerivAt_const t y)
    simpa only [zero_sub,map_neg] using hh
  have hQd (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt (fun t => ∫y,ψ (t,y) ∂μ) 0 t := by
    have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F:=fun t y => ψ (t,y)) (F':=fun t y => -(S t y (f y)))
      (Ioo_mem_nhds ht.1 ht.2)
      (Eventually.of_forall fun _ =>
        (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (him t) (hdm t).aestronglyMeasurable
      (Eventually.of_forall fun y s _ => hdb s y) (hfi.const_mul C)
      (Eventually.of_forall fun y s hs => hpd s hs y)
    have hz := hflux t
    have he : (∫y,-(S t y (f y)) ∂μ)=0 := by rw [integral_neg]; exact neg_eq_zero.mpr hz
    rw [he] at hh
    exact hh.2
  have hQc : Continuous (fun t => ∫y,ψ (t,y) ∂μ) :=
    continuous_of_dominated
      (fun _ => (hψ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun t => Eventually.of_forall (hψB t)) (integrable_const B)
      (Eventually.of_forall fun y => hψ.comp (continuous_id.prodMk continuous_const))
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (fun t => ∫y,ψ (t,y) ∂μ) hab hQc.continuousOn
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : (∫y,ψ (b,y) ∂μ)=(∫y,ψ (a,y) ∂μ) :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  have ha : (fun y => ψ (a,y))=(fun y => φ (flow (fun _ _ => hL) hc ⟨a,le_rfl,hab.le⟩ y b)) := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)]
  have hb : (fun y => ψ (b,y))=φ := by
    funext y
    dsimp [ψ]
    rw [backwardTest_eq,projIcc_of_mem _ (show b∈Icc a b from ⟨hab.le,le_rfl⟩)]
    exact congrArg φ (flow_initial (fun _ _ => hL) hc T y)
  rw [ha,hb] at heq
  exact heq.symm

end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.LinearGrowthODE
open Set Function Filter Metric MeasureTheory
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma fderiv_zero_of_vanish_outside {ψ : E → ℝ} {C : ℝ}
    (hψ : ∀z,C<‖z‖ → ψ z=0) {y : E} (hy : C<‖y‖) : fderiv ℝ ψ y=0 := by
  have he : ψ =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact hψ z hz
  exact ((hasFDerivAt_const (𝕜:=ℝ) (0:ℝ) y).congr_of_eventuallyEq he).fderiv

theorem stationary_integral_compact {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a<b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0)
    {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫y,φ (flow hf hK hB hg hab.le y b) ∂μ)=∫y,φ y ∂μ := by
  obtain ⟨R,hR,hRb⟩ := hφc.isCompact.isBounded.exists_pos_norm_le
  have hφv (z : E) (hz : R<‖z‖) : φ z=0 := by
    by_contra hh
    exact (not_lt_of_ge (hRb z (subset_tsupport φ hh))) hz
  let C := gronwallBound R K B (b-a)
  obtain ⟨n,hn⟩ := exists_nat_gt (max C (gronwallBound C K B (b-a)))
  have hnC : C≤(n:ℝ)+1 := by have := le_max_left C (gronwallBound C K B (b-a)); linarith
  have hnG : gronwallBound C K B (b-a)≤(n:ℝ)+1 := by
    have := le_max_right C (gronwallBound C K B (b-a)); linarith
  obtain ⟨L,hL⟩ := truncated_lipschitz hf n
  let hc := truncated_continuous hf n
  let T : Icc a b := ⟨b,hab.le,le_rfl⟩
  let ψ := GlobalODE.backwardTest hab.le hc (fun _ _ => hL) T φ
  have hψv (t : ℝ) (z : E) (hz : C<‖z‖) : ψ (t,z)=0 :=
    backwardTest_vanish hf hK hB hg hab.le hR.le hφv n hL t z hz
  have hψc (t : ℝ) : ContDiff ℝ 1 (fun z => ψ (t,z)) := by
    have he : (fun z => ψ (t,z))=φ ∘ (fun z =>
        GlobalODE.flow (fun _ _ => hL) hc (projIcc a b hab.le t) z T) := by
      funext z
      exact GlobalODE.backwardTest_eq hab.le hc (fun _ _ => hL) T φ (t,z)
    rw [he]
    apply hφ.comp
    apply GlobalODE.flow_contDiff_one (D:=fun _ => fderiv ℝ (truncated f n)) hab.le hc (fun _ _ => hL)
      (((truncated_smooth hf n).continuous_fderiv (by norm_num)).comp continuous_snd)
      (fun _ z => ((truncated_smooth hf n).differentiable (by norm_num) z).hasFDerivAt)
  have hψcompact (t : ℝ) : HasCompactSupport (fun z => ψ (t,z)) :=
    HasCompactSupport.intro (isCompact_closedBall (0:E) C) fun z hz =>
      hψv t z (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)
  have hψflux (t : ℝ) : (∫y,(fderiv ℝ (fun z => ψ (t,z)) y) (truncated f n y) ∂μ)=0 := by
    rw [show (fun y => (fderiv ℝ (fun z => ψ (t,z)) y) (truncated f n y))=
      (fun y => (fderiv ℝ (fun z => ψ (t,z)) y) (f y)) by
        funext y
        by_cases hy : ‖y‖≤C
        · rw [truncated_eq (hy.trans hnC)]
        · rw [fderiv_zero_of_vanish_outside (hψv t) (lt_of_not_ge hy)]
          rfl]
    exact hflux _ (hψc t) (hψcompact t)
  have hni : Integrable (fun x => ‖truncated f n x‖) μ :=
    hfi.mono' (truncated_smooth hf n).continuous.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_norm,truncated,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (PoincareCutoff.cutoff_nonneg n x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (PoincareCutoff.cutoff_le_one n x))
  obtain ⟨J,hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφ (by norm_num)
  obtain ⟨D,hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
  have hh := GlobalODE.stationary_integral_of_backward_flux (truncated_smooth hf n) hL hni
    hab hφ hJ hD hψflux
  rw [←hh]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : ‖y‖≤C
  · exact congrArg φ (eq_truncated_flow hf hK hB hg hab.le n hL hnG hy ⟨hab.le,le_rfl⟩)
  · have hy' : C<‖y‖ := lt_of_not_ge hy
    have hv : φ (flow hf hK hB hg hab.le y b)=0 := by
      apply hφv
      by_contra! h
      have hh := growth_from_right (flow_continuous hf hK hB hg hab.le y).continuousOn
        (flow_deriv hf hK hB hg hab.le y) h (fun _ _ => hg _) a ⟨le_rfl,hab.le⟩
      rw [flow_initial] at hh
      exact (not_lt_of_ge hh) hy'
    rw [hv]
    exact (by
      have hh := hψv a y hy'
      dsimp [ψ] at hh
      rw [GlobalODE.backwardTest_eq,projIcc_of_mem _ (show a∈Icc a b from ⟨le_rfl,hab.le⟩)] at hh
      exact hh.symm)
theorem stationary_law {f : E → E} (hf : ContDiff ℝ 1 f) {K B a b : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hg : ∀x,‖f x‖≤K*‖x‖+B) (hab : a<b)
    {μ : Measure E} [IsFiniteMeasure μ] (hfi : Integrable (fun x => ‖f x‖) μ)
    (hflux : ∀ψ : E → ℝ,ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫x,(fderiv ℝ ψ x) (f x) ∂μ)=0) :
    μ.map (fun y => flow hf hK hB hg hab.le y b)=μ := by
  let T := fun y => flow hf hK hB hg hab.le y b
  have hTc : Continuous T := flow_continuous_initial hf hK hB hg hab.le b ⟨hab.le,le_rfl⟩
  apply measure_eq_of_smooth_lipschitz
  intro φ hφ _hφL hφB
  obtain ⟨D,hD⟩ := hφB
  let u := PoincareCutoff.truncation φ
  have hul (η : Measure E) [IsFiniteMeasure η] :
      Tendsto (fun n => ∫y,u n y ∂η) atTop (𝓝 (∫y,φ y ∂η)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => D)
      (fun n => (PoincareCutoff.truncation_smooth hφ n).continuous.aestronglyMeasurable)
      (integrable_const D)
    · exact fun n => Eventually.of_forall fun y =>
        (PoincareCutoff.truncation_abs φ n y).trans (hD y)
    · exact Eventually.of_forall (PoincareCutoff.truncation_tendsto φ)
  have he : (fun n => ∫y,u n y ∂μ.map T)=(fun n => ∫y,u n y ∂μ) := by
    funext n
    rw [integral_map hTc.aemeasurable
      (PoincareCutoff.truncation_smooth hφ n).continuous.aestronglyMeasurable]
    exact stationary_integral_compact hf hK hB hg hab hfi hflux
      (PoincareCutoff.truncation_smooth hφ n) (PoincareCutoff.truncation_compact φ n)
  exact tendsto_nhds_unique (hul (μ.map T)) (he ▸ hul μ)
end LogConcaveSampling.LinearGrowthODE

end

end

end

end OAI
