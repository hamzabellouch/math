import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.MomentumDirection
import OAI.Analysis.VlasovMaxwell.LocalPDE.UniformParticleDensityConstant

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma momentumDirection_increment {v w : Vec} (hv : v≠0) (hw : w≠0) :
    ‖momentumDirection v-momentumDirection w‖≤2*‖v-w‖/‖v‖ := by
  have hvn : 0<‖v‖ := norm_pos_iff.mpr hv
  have hwn : ‖w‖≠0 := norm_ne_zero_iff.mpr hw
  have he : ‖v‖ • (momentumDirection v-momentumDirection w)=
      (v-w)+(‖w‖-‖v‖) • momentumDirection w := by
    simp only [momentumDirection,smul_sub,smul_smul,sub_mul,mul_inv_cancel₀ hvn.ne',
      mul_inv_cancel₀ hwn,one_smul]
    module
  have hh := norm_add_le (v-w) ((‖w‖-‖v‖) • momentumDirection w)
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos hvn,norm_smul,Real.norm_eq_abs,
    momentumDirection_norm hw,mul_one] at hh
  have hn : |‖w‖-‖v‖|≤‖v-w‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le w v
  exact (le_div_iff₀ hvn).mpr (by nlinarith)

lemma norm_momentum_of_high_band {v : Vec} {w : ℝ} (hw : 16≤w) (hq : w/8≤q v) :
    w/16≤‖v‖ := by
  have hqn := q_pos v
  have hn := norm_nonneg v
  have hqs := q_sq v
  nlinarith [sq_nonneg (q v-w/8),sq_nonneg (‖v‖-w/16)]

lemma IncrementBootstrap.direction_increment {V : ℝ→Vec} {T M A P L a b : ℝ}
    (H : IncrementBootstrap V T M A P L) (k : ℕ) (hk : 16≤(2:ℝ)^k)
    (hJ : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    {s t : ℝ} (hs : s∈Icc a b) (ht : t∈Icc a b) :
    ‖momentumDirection (V t)-momentumDirection (V s)‖≤
      (32/(2:ℝ)^k)*(M*P*Real.sqrt |t-s|+A*|t-s| *(P^2*L/(2:ℝ)^k)) := by
  have hw : 0<(2:ℝ)^k := by positivity
  have hn (r : ℝ) (hr : r∈Icc a b) : (2:ℝ)^k/16≤‖V r‖ :=
    norm_momentum_of_high_band hk (hband r hr).1
  have hn0 (r : ℝ) (hr : r∈Icc a b) : V r≠0 := by
    apply norm_pos_iff.mp
    exact (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le (hn r hr)
  have hnorm : ‖V t-V s‖≤M*P*Real.sqrt |t-s|+A*|t-s| *(P^2*L/(2:ℝ)^k) := by
    rcases le_total s t with hst|hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact H k s t (hJ hs).1 hst (hJ ht).2 (fun r hr=>hband r ⟨hs.1.trans hr.1,hr.2.trans ht.2⟩)
    · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]
      exact H k t s (hJ ht).1 hts (hJ hs).2 (fun r hr=>hband r ⟨ht.1.trans hr.1,hr.2.trans hs.2⟩)
  calc
    _ ≤ 2*‖V t-V s‖/‖V t‖ := momentumDirection_increment (hn0 t ht) (hn0 s hs)
    _ ≤ 2*‖V t-V s‖/((2:ℝ)^k/16) := div_le_div_of_nonneg_left (by positivity)
      (div_pos hw (by norm_num)) (hn t ht)
    _ = (32/(2:ℝ)^k)*‖V t-V s‖ := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)

lemma sqrt_linear_small {B C δ u : ℝ} (hB : 0<B) (hC : 0<C) (hδ : 0<δ)
    (_hu : 0≤u) (hsmall : u < min ((δ/(4*B))^2) (δ/(4*C))) :
    B*Real.sqrt u+C*u<δ := by
  have hs : Real.sqrt u<δ/(4*B) := (Real.sqrt_lt' (by positivity)).mpr (lt_of_lt_of_le hsmall (min_le_left _ _))
  have hc : u<δ/(4*C) := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hs' := (lt_div_iff₀ (show 0<4*B by positivity)).mp hs
  have hc' := (lt_div_iff₀ (show 0<4*C by positivity)).mp hc
  linarith

lemma IncrementBootstrap.finite_direction_stops {V : ℝ→Vec} {T M A P L a b δ : ℝ}
    (H : IncrementBootstrap V T M A P L) (k : ℕ) (hk : 16≤(2:ℝ)^k)
    (hab : a≤b) (hV : ContinuousOn V (Icc a b)) (hJ : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    (hM : 0<M) (hA : 0<A) (hP : 0<P) (hL : 0<L) (hδ : 0<δ) :
    let B := (32/(2:ℝ)^k)*M*P
    let C := (32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k)
    let ℓ := min ((δ/(4*B))^2) (δ/(4*C))
    ∃n : ℕ,∃t : ℕ→ℝ,t 0=a ∧ t n=b ∧
      (∀i≤n,t i∈Icc a b) ∧
      (∀i<n,t i<t (i+1) ∧
        (∀x∈Icc (t i) (t (i+1)),‖momentumDirection (V x)-momentumDirection (V (t i))‖≤δ) ∧
        (i+1<n→‖momentumDirection (V (t (i+1)))-momentumDirection (V (t i))‖=δ ∧ ℓ≤t (i+1)-t i)) := by
  dsimp only
  have hB : 0<(32/(2:ℝ)^k)*M*P := by positivity
  have hC : 0<(32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k) := by positivity
  apply exists_finite_direction_stops hab
    (continuousOn_momentumDirection hV (fun t ht=>by
      apply norm_pos_iff.mp
      exact (div_pos (pow_pos (by norm_num : (0:ℝ)<2) k) (by norm_num : (0:ℝ)<16)).trans_le
        (norm_momentum_of_high_band hk (hband t ht).1))) hδ (by positivity)
  intro s hs t ht hst
  apply (H.direction_increment k hk hJ hband hs ht).trans_lt
  convert sqrt_linear_small hB hC hδ (abs_nonneg (t-s)) hst using 1
  first | rfl | ring

def angularZeroBump (w : ℝ) (hw : 0<w) : ContDiffBump (0:Vec) :=
  ⟨w/64,w/32,by positivity,by linarith⟩

def extendedAngularCLM (w : ℝ) (hw : 0<w) (v : Vec) : Vec→L[ℝ]Vec :=
  (1-angularZeroBump w hw v) • angularMultiplierCLM w v

lemma extendedAngularCLM_contDiff (w : ℝ) (hw : 0<w) :
    ContDiff ℝ ∞ (extendedAngularCLM w hw) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v=0
  · subst v
    apply (contDiffAt_const (c:=(0:Vec→L[ℝ]Vec))).congr_of_eventuallyEq
    have he := (angularZeroBump w hw).eventuallyEq_one_of_mem_ball
      (show (0:Vec)∈ball 0 (angularZeroBump w hw).rIn by simpa only [mem_ball,dist_self,angularZeroBump] using div_pos hw (by norm_num : (0:ℝ)<64))
    filter_upwards [he] with v hv
    change (1-angularZeroBump w hw v) • angularMultiplierCLM w v=0
    simp only [hv,Pi.one_apply,sub_self]
    exact zero_smul ℝ (angularMultiplierCLM w v)
  · exact ((contDiffAt_const.sub (angularZeroBump w hw).contDiff.contDiffAt).smul
      (contDiffAt_angularMultiplierCLM w hv le_rfl))

lemma extendedAngularCLM_eq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32≤‖v‖) :
    extendedAngularCLM w hw v=angularMultiplierCLM w v := by
  have hz := (angularZeroBump w hw).zero_of_le_dist (by simpa only [dist_zero_right,angularZeroBump] using hv)
  simp only [extendedAngularCLM,hz,sub_zero,one_smul]

lemma extendedAngularCLM_eventuallyEq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) :
    extendedAngularCLM w hw =ᶠ[𝓝 v] angularMultiplierCLM w := by
  have he : ∀ᶠ z : Vec in 𝓝 v,w/32<‖z‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hv)
  filter_upwards [he] with z hz
  exact extendedAngularCLM_eq w hw hz.le

lemma hasDerivAt_extendedAngularCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (w : ℝ) (hw : 0<w) :
    HasDerivAt (fun r=>extendedAngularCLM w hw (V r))
      (fderiv ℝ (extendedAngularCLM w hw) (V t) K) t :=
  ((extendedAngularCLM_contDiff w hw).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hV

lemma extendedAngularCLM_fderiv (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) (K : Vec) :
    fderiv ℝ (extendedAngularCLM w hw) v K=angularDerivativeCLM w v K := by
  have hv0 : v≠0 := norm_pos_iff.mp ((div_pos hw (by norm_num : (0:ℝ)<32)).trans hv)
  have hcurve : HasDerivAt (fun r : ℝ=>v+r • K) K 0 := by
    convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K) using 1 <;> first | rfl | simp only [one_smul,zero_add]
  have ht : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 v) := by
    have hc : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 (v+(0:ℝ) • K)) := hcurve.continuousAt
    simpa only [zero_smul,add_zero] using hc
  have he := (extendedAngularCLM_eventuallyEq w hw hv).comp_tendsto ht
  have ha := (hasDerivAt_angularMultiplierCLM hcurve (by simpa using hv0) w).congr_of_eventuallyEq he
  have hb := hasDerivAt_extendedAngularCLM hcurve w hw
  simpa only [zero_smul,add_zero] using hb.unique ha

end RVM

end

end OAI
