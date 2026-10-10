import Mathlib
import OAI.Probability.SLELocalization.ReverseFlow
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Angular Barrier estimates. -/

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge.AngularBarrier

lemma value_decay {l b : ℝ} (hl : 0 < l) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ t q : ℝ, 1 ≤ t → 0 ≤ q →
      value l b t q ≤ K*Real.exp (-(l*b/2)*t)*q^b := by
  let c := (1-Real.exp (-l))/(2*(b+1))
  have hc : 0 < c := div_pos (sub_pos.2 (Real.exp_lt_one_iff.2 (by linarith))) (by positivity)
  have hg : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  refine ⟨1/(b*Real.Gamma b*c^b), by positivity, ?_⟩
  intro t q ht hq
  have ht0 : 0 < t := by linarith
  have ha := scale_pos hl hb ht0
  have hlower : c*Real.exp (l*t) ≤ scale l b t := by
    have hh : 1 ≤ Real.exp (l*t)*Real.exp (-l) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.2 (by nlinarith)
    dsimp only [c,scale]
    apply (le_div_iff₀ (by positivity : 0 < 2*(b+1))).2
    have heq : ((1-Real.exp (-l))/(2*(b+1))*Real.exp (l*t))*(2*(b+1)) =
        (1-Real.exp (-l))*Real.exp (l*t) := by field_simp
    rw [heq]
    nlinarith
  have hratio : q/scale l b t ≤ q/(c*Real.exp (l*t)) :=
    div_le_div_of_nonneg_left hq (mul_pos hc (Real.exp_pos _)) hlower
  have hpow := Real.rpow_le_rpow (div_nonneg hq ha.le) hratio hb.le
  have hbound := (cdf_le_power hb (div_nonneg hq ha.le)).trans
    (div_le_div_of_nonneg_right hpow (mul_pos hb hg).le)
  have he : Real.exp (l*b/2*t)*(q/(c*Real.exp (l*t)))^b/(b*Real.Gamma b) =
      1/(b*Real.Gamma b*c^b)*Real.exp (-(l*b/2)*t)*q^b := by
    rw [Real.div_rpow hq (mul_pos hc (Real.exp_pos _)).le,
      Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hratioexp : Real.exp (l*b/2*t)/Real.exp (l*t*b) = Real.exp (-(l*b/2)*t) := by
      rw [← Real.exp_sub]; congr 1; ring
    calc
      _ = (Real.exp (l*b/2*t)/Real.exp (l*t*b))*q^b/(b*Real.Gamma b*c^b) := by ring
      _ = _ := by rw [hratioexp]; ring
  calc
    _ ≤ Real.exp (l*b/2*t)*((q/(c*Real.exp (l*t)))^b/(b*Real.Gamma b)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = _ := by rw [← mul_div_assoc, he]

def squaredSine (w : ℝ) := 1/(1+w^2)

def profile (l b t w : ℝ) := value l b t (squaredSine w)

def profileT (l b t w : ℝ) := valueT l b t (squaredSine w)

def profileW (l b t w : ℝ) := (-2*w/(1+w^2)^2)*valueQ l b t (squaredSine w)

def profileWW (l b t w : ℝ) := (6*w^2-2)/(1+w^2)^3*valueQ l b t (squaredSine w) +
  4*w^2/(1+w^2)^4*valueQQ l b t (squaredSine w)

lemma squaredSine_pos (w : ℝ) : 0 < squaredSine w := by unfold squaredSine; positivity

lemma squaredSine_le_one (w : ℝ) : squaredSine w ≤ 1 := by
  unfold squaredSine; exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg w])

lemma hasDerivAt_squaredSine (w : ℝ) :
    HasDerivAt squaredSine (-2*w/(1+w^2)^2) w := by
  apply ((hasDerivAt_const w 1).div (((hasDerivAt_id w).pow 2).const_add 1) (by simp only [Pi.pow_apply, id_eq]; positivity)).congr_deriv
  simp only [Pi.pow_apply, id_eq]; ring

lemma contDiff_squaredSine (n : WithTop ℕ∞) : ContDiff ℝ n squaredSine := by
  unfold squaredSine
  exact contDiff_const.div (contDiff_const.add (contDiff_id.pow 2)) (fun w => by positivity)

lemma contDiffAt_profile {l b : ℝ} (hl : 0 < l) (hb : 0 < b) (n : ℕ)
    {v : ℝ × ℝ} (ht : 0 < v.1) :
    ContDiffAt ℝ n (fun v : ℝ × ℝ => profile l b v.1 v.2) v := by
  have hq := (contDiff_squaredSine n).contDiffAt.comp v contDiffAt_snd
  have hm : ContDiffAt ℝ n (fun v : ℝ × ℝ => (v.1,squaredSine v.2)) v :=
    contDiffAt_fst.prodMk hq
  have hh := (contDiffAt_value (v:=(v.1,squaredSine v.2)) hl hb n ht (squaredSine_pos v.2)).comp v hm
  dsimp only [Function.comp_def] at hh
  exact hh

lemma hasDerivAt_profile_w {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) (w : ℝ) :
    HasDerivAt (profile l b t) (profileW l b t w) w := by
  have hh := (hasDerivAt_value_q hl hb ht (squaredSine_pos w)).comp w (hasDerivAt_squaredSine w)
  apply hh.congr_deriv
  dsimp only [profileW]; ring

lemma hasDerivAt_profile_t {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) (w : ℝ) :
    HasDerivAt (fun s => profile l b s w) (profileT l b t w) t :=
  hasDerivAt_value_t hl hb ht (squaredSine_pos w)

lemma deriv_squaredSine_hasDerivAt (w : ℝ) :
    HasDerivAt (fun w : ℝ => -2*w/(1+w^2)^2) ((6*w^2-2)/(1+w^2)^3) w := by
  have hd := ((hasDerivAt_id w).const_mul (-2)).div
    ((((hasDerivAt_id w).pow 2).const_add 1).pow 2) (by simp only [Pi.pow_apply, id_eq]; positivity)
  apply hd.congr_deriv
  simp only [Pi.pow_apply, id_eq]
  field_simp
  ring

lemma hasDerivAt_profileW {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) (w : ℝ) :
    HasDerivAt (profileW l b t) (profileWW l b t w) w := by
  have hh := (deriv_squaredSine_hasDerivAt w).mul
    ((hasDerivAt_valueQ_q hl hb ht (squaredSine_pos w)).comp w (hasDerivAt_squaredSine w))
  apply hh.congr_deriv
  dsimp only [profileWW, Function.comp_def]
  field_simp
  ring

lemma deriv_profile {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) :
    deriv (profile l b t) = profileW l b t := funext fun w => (hasDerivAt_profile_w hl hb ht w).deriv

lemma second_profile {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) :
    iteratedDeriv 2 (profile l b t) = profileWW l b t := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_profile hl hb ht]
  exact funext fun w => (hasDerivAt_profileW hl hb ht w).deriv

lemma parameter_deriv_smooth (f : ℝ → ℝ → ℝ) (n : ℕ) {v : ℝ × ℝ}
    (hf : ContDiffAt ℝ (n+1) (Function.uncurry f) v) :
    ContDiffAt ℝ n (fun v : ℝ × ℝ => deriv (f v.1) v.2) v := by
  let g : (ℝ × ℝ) → ℝ → ℝ := fun v w => f v.1 w
  have hh : ContDiffAt ℝ (n+1) (Function.uncurry g) (v,v.2) := by
    have hm : ContDiffAt ℝ (n+1) (fun r : (ℝ × ℝ) × ℝ => (r.1.1,r.2)) (v,v.2) := by fun_prop
    exact hf.comp (v,v.2) hm
  have hd := hh.fderiv (m:=n) contDiffAt_snd (by simp)
  exact hd.clm_apply contDiffAt_const

lemma parameter_iteratedDeriv_smooth (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ∀ v : ℝ × ℝ, 0 < v.1 → ContDiffAt ℝ n (Function.uncurry f) v)
    (k n : ℕ) (v : ℝ × ℝ) (hv : 0 < v.1) :
    ContDiffAt ℝ n (fun v : ℝ × ℝ => iteratedDeriv k (f v.1) v.2) v := by
  induction k generalizing n with
  | zero => exact hf n v hv
  | succ k ih =>
    simpa only [iteratedDeriv_succ] using parameter_deriv_smooth (fun t => iteratedDeriv k (f t)) n (ih (n+1))

lemma profile_derivative_continuousAt {l b : ℝ} (hl : 0 < l) (hb : 0 < b)
    (k : ℕ) {v : ℝ × ℝ} (hv : 0 < v.1) :
    ContinuousAt (fun v : ℝ × ℝ => iteratedDeriv k (profile l b v.1) v.2) v :=
  (parameter_iteratedDeriv_smooth (profile l b) (fun n _v hv => contDiffAt_profile hl hb n hv)
    k 0 v hv).continuousAt

lemma profile_super {κ t : ℝ} (hκ : 0 < κ ∧ κ < 8) (ht : 0 < t) (w : ℝ) :
    w*(1+w^2)*profileW (κ/2) ((8/κ-1)/2) t w +
      κ/8*(1+w^2)^2*profileWW (κ/2) ((8/κ-1)/2) t w ≤
        profileT (κ/2) ((8/κ-1)/2) t w := by
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have hi := supersolution (l:=κ/2) (b:=(8/κ-1)/2) (t:=t) (q:=squaredSine w) (div_pos hκ.1 (by norm_num)) hb ht (squaredSine_pos w) (squaredSine_le_one w)
  change _ ≤ valueT (κ/2) ((8/κ-1)/2) t (squaredSine w)
  convert hi using 1
  dsimp only [profileW, profileWW, squaredSine]
  field_simp [hκ.1.ne']
  ring

lemma hasDerivAt_value_path {l b : ℝ} (hl : 0 < l) (hb : 0 < b)
    {T Q : ℝ → ℝ} {s T' Q' : ℝ} (hT : HasDerivAt T T' s) (hQ : HasDerivAt Q Q' s)
    (ht : 0 < T s) (hq : 0 < Q s) :
    HasDerivAt (fun v => value l b (T v) (Q v))
      (valueT l b (T s) (Q s)*T' + valueQ l b (T s) (Q s)*Q') s := by
  have ha := (hasDerivAt_scale l b (T s)).comp s hT
  have hs := scale_pos hl hb ht
  have hh := ((hT.const_mul (l*b/2)).exp).mul
    ((hasDerivAt_cdf hb (div_pos hq hs)).comp s (hQ.div ha hs.ne'))
  apply hh.congr_deriv
  simp only [Function.comp_def, Pi.div_apply]
  dsimp only [valueT, valueQ, value]
  have he : Real.exp (l*T s) = 2*(b+1)*scale l b (T s)+1 := by unfold scale; field_simp; ring
  rw [he]
  field_simp
  ring

lemma hasDerivAt_profile_path {l b : ℝ} (hl : 0 < l) (hb : 0 < b)
    {T W : ℝ → ℝ} {s T' W' : ℝ} (hT : HasDerivAt T T' s) (hW : HasDerivAt W W' s)
    (ht : 0 < T s) :
    HasDerivAt (fun v => profile l b (T v) (W v))
      (profileT l b (T s) (W s)*T' + profileW l b (T s) (W s)*W') s := by
  have hq := (hasDerivAt_squaredSine (W s)).comp s hW
  have hh := hasDerivAt_value_path hl hb hT hq ht (squaredSine_pos (W s))
  apply hh.congr_deriv
  simp only [profileT,profileW,Function.comp_def]
  ring

lemma profile_smooth {l b t : ℝ} (hl : 0 < l) (hb : 0 < b) (ht : 0 < t) (n : ℕ) :
    ContDiff ℝ n (profile l b t) := by
  apply contDiff_iff_contDiffAt.2
  intro w
  have hh := (contDiffAt_profile (v:=(t,w)) hl hb n ht).comp w (contDiffAt_const.prodMk contDiffAt_id)
  dsimp only [Function.comp_def] at hh
  exact hh

lemma iteratedDeriv_affine (f : ℝ → ℝ) (hf : ∀ n : ℕ, ContDiff ℝ n f) (k : ℕ) (a c x : ℝ) :
    iteratedDeriv k (fun x => f (a*x+c)) x = a^k*iteratedDeriv k f (a*x+c) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have he : iteratedDeriv k (fun x => f (a*x+c)) = fun x => a^k*iteratedDeriv k f (a*x+c) := funext ih
    rw [iteratedDeriv_succ, he]
    have hd : Differentiable ℝ (iteratedDeriv k f) :=
      ContDiff.differentiable_iteratedDeriv k (hf (k+1)) (by exact_mod_cast Nat.lt_succ_self k)
    have hh := ((hd (a*x+c)).hasDerivAt.comp x
      (((hasDerivAt_id x).const_mul a).add_const c)).const_mul (a^k)
    dsimp only [Function.comp_def, id_eq] at hh
    rw [hh.deriv]
    simp only [iteratedDeriv_succ,pow_succ,mul_one]
    ring

end SLEExactGauge.AngularBarrier

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianLocal
open BrownianPredictable PredictableLimit BrownianIto TaylorMeshes TimeField
open BrownianField BrownianStopped PartitionMeshes StoppedMeshes

structure LocalRegular (F V : ℝ → ℝ → ℝ) (b : ℝ → ℝ) (T : ℝ) : Prop where
  smooth : ∀ t, ContDiff ℝ 3 (F t)
  third_cont : ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv 3 (F p.1) p.2) ((Icc 0 T) ×ˢ univ)
  time_cont : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T)
  time_deriv : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun u => F u x) (V t x) t
  drift_cont : ContinuousOn (fun p : ℝ × ℝ => V p.1 (b p.2)) ((Icc 0 T) ×ˢ (Icc 0 T))
  second_cont : ContinuousOn (fun t => iteratedDeriv 2 (F t) (b t)) (Icc 0 T)

lemma family_remainder_tendsto_of_eventually_bounded {T : ℝ} (p : PartitionSequence T)
    {f : ℕ → ℕ → ℝ → ℝ} {b : ℝ → ℝ}
    (hf : ∀ n i, ContDiff ℝ 3 (f n i)) {V K : ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (hV : 0 ≤ V) (hK : 0 ≤ K)
    (h3 : ∀ n i, i < p.count n → ∀ x ∈ uIcc (b (p.time n i)) (b (p.time n (i+1))),
      |iteratedDeriv 3 (f n i) x| ≤ K)
    (hQ : ∀ᶠ n in atTop, (∑ i ∈ Finset.range (p.count n),
      (b (p.time n (i+1))-b (p.time n i))^2) ≤ V) :
    Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      remainder₂ (f n i) (b (p.time n i)) (b (p.time n (i+1)))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ := ε / ((K+1)*(V+1))
  have hδ : 0 < δ := div_pos hε (mul_pos (by linarith) (by linarith))
  have hs := p.increments_small hb hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.and hQ)
  refine ⟨N, fun n hn => ?_⟩
  rcases hN n hn with ⟨hs, hq⟩
  have hr := sum_family_remainder₂_bound (hf n) (fun i => b (p.time n i))
    (p.count n) K δ hK hδ.le (fun i hi z hz => h3 n i hi z hz) (fun i hi => (hs i hi).le)
  simp only [Real.dist_eq, sub_zero]
  calc
    _ ≤ K * δ / 6 * ∑ i ∈ Finset.range (p.count n),
        (b (p.time n (i+1))-b (p.time n i))^2 := hr
    _ ≤ K * δ / 6 * (V+1) :=
      mul_le_mul_of_nonneg_left (hq.trans (by linarith)) (by positivity)
    _ < ε := by
      dsimp [δ]
      have hden : 0 < (K+1)*(V+1) := mul_pos (by linarith) (by linarith)
      have hid : K * (ε / ((K+1)*(V+1))) / 6 * (V+1) = ε * (K / (6*(K+1))) := by
        field_simp
      rw [hid]
      have hk : K / (6*(K+1)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      simpa using mul_lt_mul_of_pos_left hk hε

lemma stopped_field_taylor_limit {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 ≤ τ) (hτT : τ ≤ T)
    {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hb : ContinuousOn b (Icc 0 T)) (hreg : LocalRegular F V b τ)
    (hQ : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1)) - b (mesh T n i))^2) atTop (𝓝 T))
    {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hA : ∀ n i, mesh T n i < τ →
      |deriv (F (mesh T n i)) (b (mesh T n i))| ≤ K₁)
    (hC : ∀ n i, mesh T n i < τ →
      |iteratedDeriv 2 (F (mesh T n i)) (b (mesh T n i))| ≤ K₂)
    (hE : Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
      iteratedDeriv 2 (F (mesh T n i)) (b (mesh T n i)) *
        ((b (mesh T n (i+1)) - b (mesh T n i))^2 - T/(2 : ℝ)^n) else 0) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
      deriv (F (mesh T n i)) (b (mesh T n i)) *
        (b (mesh T n (i+1)) - b (mesh T n i)) else 0) atTop
      (𝓝 (F τ (b τ) - F 0 (b 0) - (∫ t in (0 : ℝ)..τ, V t (b t)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..τ, iteratedDeriv 2 (F t) (b t))) := by
  let p := clippedDyadic T τ hT hτ hτT
  let C : ℝ → ℝ := fun t => iteratedDeriv 2 (F t) (b t)
  let A : ℝ → ℝ := fun t => deriv (F t) (b t)
  have hbτ := hb.mono (Icc_subset_Icc le_rfl hτT)
  have hQc := clipped_quadratic_eventually_bounded hT hτ hτT hb hQ
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hbτ
  have hc := hreg.third_cont.mono (Set.prod_mono Subset.rfl (subset_univ (Icc (-R) R)))
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  have hr := family_remainder_tendsto_of_eventually_bounded p
    (f := fun n i => F (p.time n i)) (fun _ _ => hreg.smooth _)
    hbτ (show 0 ≤ T+2 by linarith) (le_max_left 0 K) (fun n i hi x hx => by
      have hleft : b (p.time n i) ∈ Icc (-R) R := abs_le.1 (by simpa only [Real.norm_eq_abs] using hR _ (p.mem n i hi.le))
      have hright : b (p.time n (i+1)) ∈ Icc (-R) R := abs_le.1 (by simpa only [Real.norm_eq_abs] using hR _ (p.mem n (i+1) hi))
      have hkx := hK (p.time n i,x) ⟨p.mem n i hi.le, uIcc_subset_Icc hleft hright hx⟩
      rw [Real.norm_eq_abs] at hkx
      exact hkx.trans (le_max_right 0 K)) hQc
  have htime := p.time_increment_tendsto hreg.time_cont hreg.time_deriv hreg.drift_cont
  have hriem := prestop_riemann_tendsto hT hτ hτT hreg.second_cont
  let Qpred : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
    C (mesh T n i) * (b (mesh T n (i+1)) - b (mesh T n i))^2 else 0
  have hQpred : Tendsto Qpred atTop (𝓝 (∫ t in (0 : ℝ)..τ, C t)) := by
    have heq (n : ℕ) : Qpred n =
      (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then
        C (mesh T n i) * ((b (mesh T n (i+1))-b (mesh T n i))^2-T/(2 : ℝ)^n) else 0) +
      (∑ i ∈ Finset.range (2^n), if mesh T n i < τ then C (mesh T n i)*(T/(2 : ℝ)^n) else 0) := by
      unfold Qpred
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    dsimp only [C] at heq
    simpa only [← heq, zero_add] using hE.add hriem
  have hQdiff := clipped_quadraticSum_difference_tendsto hT hτ hτT hb
    (fun n i => C (p.time n i))
    (K := max K₂ |C τ|) (hK₂.trans (le_max_left _ _))
    (coefficient_clipped_bound C hC)
  have hQeq (n i : ℕ) :
      (if mesh T n i < τ then C (p.time n i) *
        (b (mesh T n (i+1))-b (mesh T n i))^2 else 0) =
      (if mesh T n i < τ then C (mesh T n i) *
        (b (mesh T n (i+1))-b (mesh T n i))^2 else 0) := by
    split_ifs with h
    · simp only [p, clippedDyadic, min_eq_left h.le]
    · rfl
  simp only [hQeq] at hQdiff
  have hQweighted : Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      C (p.time n i) * (b (p.time n (i+1)) - b (p.time n i))^2) atTop
      (𝓝 (∫ t in (0 : ℝ)..τ, C t)) := by
    simpa only [Qpred, sub_add_cancel, zero_add, p, clippedDyadic] using hQdiff.add hQpred
  have hTel (n : ℕ) : ∑ i ∈ Finset.range (p.count n),
      (F (p.time n (i+1)) (b (p.time n (i+1))) -
        F (p.time n i) (b (p.time n i))) = F τ (b τ) - F 0 (b 0) := by
    rw [Finset.sum_range_sub (fun i => F (p.time n i) (b (p.time n i))), p.start, p.finish]
  have hIdentity (n : ℕ) : (∑ i ∈ Finset.range (p.count n),
      A (p.time n i)*(b (p.time n (i+1))-b (p.time n i))) =
      F τ (b τ) - F 0 (b 0) -
      (∑ i ∈ Finset.range (p.count n),
        (F (p.time n (i+1)) (b (p.time n (i+1))) -
          F (p.time n i) (b (p.time n (i+1))))) - (1/2 : ℝ)*
      (∑ i ∈ Finset.range (p.count n),
        C (p.time n i)*(b (p.time n (i+1))-b (p.time n i))^2) -
      (∑ i ∈ Finset.range (p.count n), remainder₂ (F (p.time n i))
        (b (p.time n i)) (b (p.time n (i+1)))) := by
    rw [← hTel n]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [A, C, remainder₂, iteratedDeriv_succ, iteratedDeriv_zero]
    ring
  have hAclip : Tendsto (fun n => ∑ i ∈ Finset.range (p.count n),
      A (p.time n i)*(b (p.time n (i+1))-b (p.time n i))) atTop
      (𝓝 (F τ (b τ) - F 0 (b 0) - (∫ t in (0 : ℝ)..τ, V t (b t)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..τ, C t)) := by
    have hh := (((tendsto_const_nhds (x := F τ (b τ) - F 0 (b 0))).sub
      htime).sub (hQweighted.const_mul (1/2 : ℝ))).sub hr
    simpa only [← hIdentity, sub_zero] using hh
  have hAdiff := clipped_linearSum_difference_tendsto hT hτ hτT hb
    (fun n i => A (p.time n i))
    (K := max K₁ |A τ|) (hK₁.trans (le_max_left _ _))
    (coefficient_clipped_bound A hA)
  have hAeq (n i : ℕ) :
      (if mesh T n i < τ then A (p.time n i) *
        (b (mesh T n (i+1))-b (mesh T n i)) else 0) =
      (if mesh T n i < τ then A (mesh T n i) *
        (b (mesh T n (i+1))-b (mesh T n i)) else 0) := by
    split_ifs with h
    · simp only [p, clippedDyadic, min_eq_left h.le]
    · rfl
  simp only [hAeq] at hAdiff
  have hh := hAclip.sub hAdiff
  simpa only [p, clippedDyadic, A, C, sub_sub_cancel, sub_zero] using hh

theorem stopped_fieldSum_tendsto_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (τ : Ω → ℝ) (F V : Ω → ℝ → ℝ → ℝ)
    (hτ : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T)
    (hreg : ∀ᵐ sample ∂P, LocalRegular (F sample) (V sample) (fun t => B t.toNNReal sample) (τ sample))
    (C : ℕ → ℕ → Ω → ℝ)
    (hCeq : ∀ n i, C n i =ᵐ[P] stoppedCoeff 2 B T τ F n i)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ sample ∂P, |stoppedCoeff 2 B T τ F n i sample| ≤ K₂)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ sample ∂P, |stoppedCoeff 1 B T τ F n i sample| ≤ K₁) :
    ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T (stoppedCoeff 1 B T τ F) n sample) atTop
      (𝓝 (F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
        (∫ t in (0 : ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
        (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ sample),
          iteratedDeriv 2 (F sample t) (B t.toNNReal sample))) := by
  have he := brownian_dyadic_weighted_quadraticError_tendsto hB T
    C hC hC2 K₂ hK₂ (fun n i => by
      filter_upwards [hCeq n i, hbound n i] with sample he hb
      simpa only [he] using hb)
  have hCeq_all : ∀ᵐ sample ∂P, ∀ n i, C n i sample = stoppedCoeff 2 B T τ F n i sample :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hCeq n))
  have hC_all : ∀ᵐ sample ∂P, ∀ n i, |stoppedCoeff 2 B T τ F n i sample| ≤ K₂ :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hbound n))
  have hA_all : ∀ᵐ sample ∂P, ∀ n i, |stoppedCoeff 1 B T τ F n i sample| ≤ K₁ :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAbound n))
  filter_upwards [hB.cont, quadraticSum_tendsto hB T, he, hreg, hτ, hC_all, hA_all, hCeq_all]
    with sample hb hQ hE hr hτsample hCsample hAsample hCeqsample
  have hEs : Tendsto (fun n => dyadicQuadraticError B T (stoppedCoeff 2 B T τ F) n sample) atTop (𝓝 0) := by
    convert hE using 1
    funext n
    unfold dyadicQuadraticError
    simp only [hCeqsample]
  let b : ℝ → ℝ := fun t => B t.toNNReal sample
  have hbc : Continuous b := hb.comp continuous_real_toNNReal
  have hQ' : Tendsto (fun n => ∑ i ∈ Finset.range (2^n),
      (b (mesh T n (i+1))-b (mesh T n i))^2) atTop (𝓝 (T : ℝ)) := by
    simpa only [quadraticSum, b, mesh_toNNReal] using hQ
  have hE' : Tendsto (fun n => ∑ i ∈ Finset.range (2^n), if mesh T n i < τ sample then
      iteratedDeriv 2 (F sample (mesh T n i)) (b (mesh T n i)) *
        ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ)/(2 : ℝ)^n) else 0)
        atTop (𝓝 0) := by
    have heq (n : ℕ) : dyadicQuadraticError B T (stoppedCoeff 2 B T τ F) n sample =
        ∑ i ∈ Finset.range (2^n), if mesh T n i < τ sample then
          iteratedDeriv 2 (F sample (mesh T n i)) (b (mesh T n i)) *
            ((b (mesh T n (i+1))-b (mesh T n i))^2 - (T : ℝ)/(2 : ℝ)^n) else 0 := by
      unfold dyadicQuadraticError
      apply Finset.sum_congr rfl
      intro i hi
      simp only [stoppedCoeff, b, mesh_toNNReal]
      split_ifs <;> simp
    simpa only [heq] using hEs
  have hA' (n i : ℕ) (hi : mesh T n i < τ sample) :
      |deriv (F sample (mesh T n i)) (b (mesh T n i))| ≤ K₁ := by
    simpa only [stoppedCoeff, ite_eq_left hi, iteratedDeriv_succ, iteratedDeriv_zero,
      b, mesh_toNNReal] using hAsample n i
  have hC' (n i : ℕ) (hi : mesh T n i < τ sample) :
      |iteratedDeriv 2 (F sample (mesh T n i)) (b (mesh T n i))| ≤ K₂ := by
    simpa only [stoppedCoeff, ite_eq_left hi, b, mesh_toNNReal] using hCsample n i
  have ht := stopped_field_taylor_limit T.coe_nonneg hτsample.1 hτsample.2 hbc.continuousOn
    hr hQ' hK₁ hK₂ hA' hC' hE'
  have heq (n : ℕ) : dyadicDriverSum B T (stoppedCoeff 1 B T τ F) n sample =
      ∑ i ∈ Finset.range (2^n), if mesh T n i < τ sample then
        deriv (F sample (mesh T n i)) (b (mesh T n i)) *
          (b (mesh T n (i+1))-b (mesh T n i)) else 0 := by
    unfold dyadicDriverSum
    apply Finset.sum_congr rfl
    intro i hi
    simp only [stoppedCoeff, b, mesh_toNNReal, iteratedDeriv_succ, iteratedDeriv_zero]
    split_ifs <;> simp
  simpa only [← heq, b, Real.toNNReal_zero] using ht

theorem stopped_field_ito_centered_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (T : ℝ≥0)
    (τ : Ω → ℝ) (F V : Ω → ℝ → ℝ → ℝ)
    (hτ : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T)
    (hreg : ∀ᵐ sample ∂P, LocalRegular (F sample) (V sample) (fun t => B t.toNNReal sample) (τ sample))
    (A C : ℕ → ℕ → Ω → ℝ)
    (hAeq : ∀ n i, A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i)
    (hCeq : ∀ n i, C n i =ᵐ[P] stoppedCoeff 2 B T τ F n i)
    (hC : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (C n i))
    (hC2 : ∀ n i, MemLp (C n i) 2 P)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hbound : ∀ n i, ∀ᵐ sample ∂P, |stoppedCoeff 2 B T τ F n i sample| ≤ K₂)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (A n i))
    (hA2 : ∀ n i, MemLp (A n i) 2 P)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hAbound : ∀ n i, ∀ᵐ sample ∂P, |stoppedCoeff 1 B T τ F n i sample| ≤ K₁) :
    let Y := fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0 : ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2 : ℝ) * ∫ t in (0 : ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)
    Integrable Y P ∧ (∫ sample, Y sample ∂P) = 0 := by
  have ht := stopped_fieldSum_tendsto_ae hB T τ F V hτ hreg C hCeq hC hC2
    K₂ hK₂ hbound K₁ hK₁ hAbound
  have hAeq_all : ∀ᵐ sample ∂P, ∀ n i, A n i sample = stoppedCoeff 1 B T τ F n i sample :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAeq n))
  apply limit_centered hB T A hA hA2 K₁ hK₁ ?_ _ ?_
  · intro n i
    filter_upwards [hAeq n i, hAbound n i] with sample he hb
    simpa only [he] using hb
  · filter_upwards [ht, hAeq_all] with sample hsample he
    convert hsample using 1
    funext n
    unfold dyadicDriverSum
    simp only [he]

end SLEExactGauge.BrownianLocal

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.AngularBarrier

lemma profileT_continuousAt {l b : ℝ} (hl : 0 < l) (hb : 0 < b)
    {v : ℝ × ℝ} (hv : 0 < v.1) :
    ContinuousAt (fun v : ℝ × ℝ => profileT l b v.1 v.2) v := by
  have hs : ContinuousAt (fun v : ℝ × ℝ => scale l b v.1) v := by
    unfold scale; fun_prop
  have hq := (contDiff_squaredSine 0).continuous.continuousAt.comp (continuousAt_snd : ContinuousAt (fun v : ℝ × ℝ => v.2) v)
  have hz : ContinuousAt (fun v : ℝ × ℝ => squaredSine v.2 / scale l b v.1) v := hq.div hs (scale_pos hl hb hv).ne'
  have hp : ContinuousAt (fun v : ℝ × ℝ => pdf b (squaredSine v.2 / scale l b v.1)) v := (hasDerivAt_pdf hb (div_pos (squaredSine_pos v.2) (scale_pos hl hb hv))).continuousAt.comp_of_eq hz rfl
  have hf := (contDiffAt_profile hl hb 0 hv).continuousAt
  have he : ContinuousAt (fun v : ℝ × ℝ => Real.exp (l*b/2*v.1)) v := by fun_prop
  have hc : ContinuousAt (fun v : ℝ × ℝ => l+l/(2*(b+1)*scale l b v.1)) v :=
    continuousAt_const.add (continuousAt_const.div (continuousAt_const.mul hs)
      (mul_ne_zero (by positivity) (scale_pos hl hb hv).ne'))
  exact (continuousAt_const.mul hf).sub (((he.mul hp).mul hz).mul hc)

end SLEExactGauge.AngularBarrier

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.GammaField
open LoewnerCutoff LoewnerField LoewnerExit AngularBarrier
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

def rawRemaining (η ρ : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  η + Real.log (2*height hε hT U z t) - logDerivative hε hT U z t - Real.log ρ

def remaining (η ρ : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  max η (rawRemaining hε hT η ρ U z t)

def angleRatio (sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ) : ℝ :=
  ((position hε hT U z t).re-sdev*x)/height hε hT U z t

def field (l b η ρ sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ) : ℝ :=
  profile l b (remaining hε hT η ρ U z t) (angleRatio hε hT sdev U z t x)

def drift (l b η ρ sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ) : ℝ :=
  let y := height hε hT U z t
  let w := angleRatio hε hT sdev U z t x
  let v := velocity ε (extendDriver T U t) (position hε hT U z t)
  profileT l b (remaining hε hT η ρ U z t) w *
    (v.im/y - variation hε hT U z t) +
  profileW l b (remaining hε hT η ρ U z t) w * (v.re/y-w*v.im/y)

lemma remaining_pos {η : ℝ} (hη : 0 < η) (ρ : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    0 < remaining hε hT η ρ U z t := hη.trans_le (le_max_left _ _)

lemma continuous_height (z : ℂ) :
    Continuous (fun v : C(I, ℝ) × ℝ => height hε hT v.1 z v.2) :=
  continuous_const.max (Complex.continuous_im.comp (continuous_position hε hT z))

lemma continuous_rawRemaining (η ρ : ℝ) (z : ℂ) :
    Continuous (fun v : C(I, ℝ) × ℝ => rawRemaining hε hT η ρ v.1 z v.2) := by
  exact ((continuous_const.add ((continuous_const.mul (continuous_height hε hT z)).log
    (fun v => (mul_pos (by norm_num) (height_pos hε hT v.1 z v.2)).ne'))).sub
    (continuous_logDerivative hε hT z)).sub continuous_const

lemma continuous_remaining (η ρ : ℝ) (z : ℂ) :
    Continuous (fun v : C(I, ℝ) × ℝ => remaining hε hT η ρ v.1 z v.2) :=
  continuous_const.max (continuous_rawRemaining hε hT η ρ z)

lemma continuous_angleRatio (sdev : ℝ) (z : ℂ) :
    Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => angleRatio hε hT sdev v.1.1 z v.1.2 v.2) := by
  have hp := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))
  have hy := (continuous_height hε hT z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))
  exact ((Complex.continuous_re.comp hp).sub (continuous_const.mul continuous_snd)).div hy
    (fun v => (height_pos hε hT v.1.1 z v.1.2).ne')

lemma smooth {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ) (n : ℕ) :
    ContDiff ℝ n (field hε hT l b η ρ sdev U z t) := by
  apply (profile_smooth hl hb (remaining_pos hε hT hη ρ U z t) n).comp
  unfold angleRatio
  fun_prop

lemma iteratedDeriv_eq {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ) (k : ℕ) :
    iteratedDeriv k (field hε hT l b η ρ sdev U z t) x =
      (-sdev/height hε hT U z t)^k *
        iteratedDeriv k (profile l b (remaining hε hT η ρ U z t)) (angleRatio hε hT sdev U z t x) := by
  have he : field hε hT l b η ρ sdev U z t = fun x =>
      profile l b (remaining hε hT η ρ U z t)
        ((-sdev/height hε hT U z t)*x+(position hε hT U z t).re/height hε hT U z t) := by
    funext x; unfold field angleRatio; congr 1; ring
  rw [he, iteratedDeriv_affine _ (profile_smooth hl hb (remaining_pos hε hT hη ρ U z t))]
  congr 2
  unfold angleRatio; ring

lemma continuous_derivative {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev : ℝ) (z : ℂ) (k : ℕ) :
    Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => iteratedDeriv k (field hε hT l b η ρ sdev v.1.1 z v.1.2) v.2) := by
  simp only [iteratedDeriv_eq hε hT hl hb hη]
  apply continuous_iff_continuousAt.2
  intro v
  have ht := ((continuous_remaining hε hT η ρ z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))).continuousAt (x := v)
  have hw := (continuous_angleRatio hε hT sdev z).continuousAt (x := v)
  have hh := (profile_derivative_continuousAt hl hb k (remaining_pos hε hT hη ρ v.1.1 z v.1.2)).comp (ht.prodMk hw)
  exact ((continuousAt_const.div ((continuous_height hε hT z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))).continuousAt
    (height_pos hε hT v.1.1 z v.1.2).ne').pow k).mul hh

lemma continuous_field {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev : ℝ) (z : ℂ) :
    Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => field hε hT l b η ρ sdev v.1.1 z v.1.2 v.2) := by
  simpa using continuous_derivative hε hT hl hb hη ρ sdev z 0

lemma continuous_drift {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev : ℝ) (z : ℂ) :
    Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => drift hε hT l b η ρ sdev v.1.1 z v.1.2 v.2) := by
  apply continuous_iff_continuousAt.2
  intro v
  have hR := ((continuous_remaining hε hT η ρ z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))).continuousAt (x := v)
  have hW := (continuous_angleRatio hε hT sdev z).continuousAt (x := v)
  have htime := (profileT_continuousAt hl hb (remaining_pos hε hT hη ρ v.1.1 z v.1.2)).comp (hR.prodMk hW)
  have hspace := (profile_derivative_continuousAt hl hb 1 (remaining_pos hε hT hη ρ v.1.1 z v.1.2)).comp (hR.prodMk hW)
  have hspace' : ContinuousAt (fun v : (C(I, ℝ) × ℝ) × ℝ => profileW l b
      (remaining hε hT η ρ v.1.1 z v.1.2) (angleRatio hε hT sdev v.1.1 z v.1.2 v.2)) v := by
    simpa only [Function.comp_def, iteratedDeriv_succ, iteratedDeriv_zero,
      deriv_profile hl hb (remaining_pos hε hT hη ρ _ _ _)] using hspace
  have hp := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))
  have hd := (continuous_joint_extendDriver T).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))
  have hv := ((continuous_velocity hε).comp (hd.prodMk hp)).continuousAt (x := v)
  have hy := ((continuous_height hε hT z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))).continuousAt (x := v)
  have hn := (height_pos hε hT v.1.1 z v.1.2).ne'
  exact (htime.mul (((Complex.continuous_im.continuousAt.comp hv).div hy hn).sub
    ((continuous_variation hε hT z).comp (continuous_fst : Continuous (fun v : (C(I, ℝ) × ℝ) × ℝ => v.1))).continuousAt (x := v))).add
      (hspace'.mul (((Complex.continuous_re.continuousAt.comp hv).div hy hn).sub
        ((hW.mul (Complex.continuous_im.continuousAt.comp hv)).div hy hn)))

lemma rawRemaining_eq (η ρ : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ)
    (hy : ε ≤ (position hε hT U z t).im) :
    rawRemaining hε hT η ρ U z t = η + Real.log (radius hε hT U z t) - Real.log ρ := by
  have hz := hε.trans_le hy
  unfold rawRemaining radius height
  rw [max_eq_right hy, Real.log_div (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  ring

lemma rawRemaining_gt (η : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ)
    (hy : ε ≤ (position hε hT U z t).im) (hr : ρ < radius hε hT U z t) :
    η < rawRemaining hε hT η ρ U z t := by
  rw [rawRemaining_eq hε hT η ρ U z t hy]
  have hh := Real.strictMonoOn_log hρ (hρ.trans hr) hr
  linarith

lemma time_deriv {l b η ρ : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (hρ : 0 < ρ)
    (sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (hy : ε < (position hε hT U z t).im)
    (hr : ρ < radius hε hT U z t) (x : ℝ) :
    HasDerivAt (fun s => field hε hT l b η ρ sdev U z s x) (drift hε hT l b η ρ sdev U z t x) t := by
  have hH := position_deriv hε hT U z ht
  have hL := hasDerivAt_logDerivative hε hT U z ht
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hH
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hH
  dsimp only [Function.comp_def, Complex.imCLM_apply, Complex.reCLM_apply] at hIm hRe
  have hY : HasDerivAt (height hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)).im t := by
    apply hIm.congr_of_eventuallyEq
    filter_upwards [hIm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hy)] with s hs
    exact max_eq_right hs.le
  have hraw : HasDerivAt (rawRemaining hε hT η ρ U z)
      ((velocity ε (extendDriver T U t) (position hε hT U z t)).im / height hε hT U z t -
        variation hε hT U z t) t := by
    have hh := (((hY.const_mul 2).log (by have := height_pos hε hT U z t; positivity)).const_add η).sub hL
    apply (hh.sub_const (Real.log ρ)).congr_deriv
    ring
  have hR : HasDerivAt (remaining hε hT η ρ U z)
      ((velocity ε (extendDriver T U t) (position hε hT U z t)).im / height hε hT U z t -
        variation hε hT U z t) t := by
    apply hraw.congr_of_eventuallyEq
    have hh := rawRemaining_gt hε hT η hρ U z t hy.le hr
    filter_upwards [hraw.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hh)] with s hs
    exact max_eq_right hs.le
  have hW : HasDerivAt (fun s => angleRatio hε hT sdev U z s x)
      ((velocity ε (extendDriver T U t) (position hε hT U z t)).re / height hε hT U z t -
        angleRatio hε hT sdev U z t x * (velocity ε (extendDriver T U t) (position hε hT U z t)).im / height hε hT U z t) t := by
    apply ((hRe.sub_const (sdev*x)).div hY (height_pos hε hT U z t).ne').congr_deriv
    dsimp only [angleRatio]
    field_simp
  exact hasDerivAt_profile_path hl hb hR hW (remaining_pos hε hT hη ρ U z t)

lemma field_prefix_eq {ε S T : ℝ} (hε : 0 < ε) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S ≤ T) (U V : C(I, ℝ)) (z : ℂ) (l b η ρ sdev : ℝ)
    (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S))
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    field hε hS l b η ρ sdev U z t = field hε hT l b η ρ sdev V z t := by
  have hH := position_prefix_eq hε hS hT hS le_rfl hST U V z hUV ht
  have hL := logDerivative_prefix_eq hε hS hT hS le_rfl hST U V z hUV ht
  funext x
  simp only [field, remaining, rawRemaining, angleRatio, height, hH, hL]

lemma regular {l b η ρ : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (hρ : 0 < ρ)
    (hTp : 0 < T) (sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (δ : ℝ)
    (B : ℝ → ℝ) (hB : Continuous B) :
    BrownianLocal.LocalRegular (field hε hT l b η ρ sdev U z)
      (drift hε hT l b η ρ sdev U z) B (stop hε hT U z ρ δ) := by
  constructor
  · intro t; exact smooth hε hT hl hb hη ρ sdev U z t 3
  · have hm : Continuous (fun v : ℝ × ℝ => ((U,v.1),v.2)) :=
      (continuous_const.prodMk continuous_fst).prodMk continuous_snd
    exact ((continuous_derivative hε hT hl hb hη ρ sdev z 3).comp hm).continuousOn
  · intro x
    have hm : Continuous (fun t : ℝ => ((U,t),x)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    exact ((continuous_field hε hT hl hb hη ρ sdev z).comp hm).continuousOn
  · intro t ht x
    have htT : t ∈ Ioo 0 T := ⟨ht.1,ht.2.trans_le (stop_bounds hε hT U z ρ δ).2⟩
    have hh := (deficit_pos_iff hε hT U z ρ δ t).1
      (positive_before hε hT hTp U z ρ δ ht.1.le ht.2)
    exact time_deriv hε hT hl hb hη hρ sdev U z htT hh.2.1 hh.1 x
  · have hm : Continuous (fun v : ℝ × ℝ => ((U,v.1),B v.2)) :=
      (continuous_const.prodMk continuous_fst).prodMk (hB.comp continuous_snd)
    exact ((continuous_drift hε hT hl hb hη ρ sdev z).comp hm).continuousOn
  · have hm : Continuous (fun t : ℝ => ((U,t),B t)) :=
      (continuous_const.prodMk continuous_id).prodMk hB
    exact ((continuous_derivative hε hT hl hb hη ρ sdev z 2).comp hm).continuousOn

lemma coefficient_bound {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev M D : ℝ) (z : ℂ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : C(I, ℝ)) (t x : ℝ),
      remaining hε hT η ρ U z t ≤ M → |angleRatio hε hT sdev U z t x| ≤ D →
      |iteratedDeriv k (field hε hT l b η ρ sdev U z t) x| ≤ K := by
  have hc : ContinuousOn (fun v : ℝ × ℝ => iteratedDeriv k (profile l b v.1) v.2)
      ((Icc η M) ×ˢ (Icc (-D) D)) := by
    intro v hv
    exact (profile_derivative_continuousAt hl hb k (hη.trans_le hv.1.1)).continuousWithinAt
  obtain ⟨K,hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨(|sdev|/ε)^k * max 0 K, by positivity, ?_⟩
  intro U t x ht hw
  rw [iteratedDeriv_eq hε hT hl hb hη, abs_mul, abs_pow, abs_div, abs_neg,
    abs_of_pos (height_pos hε hT U z t)]
  apply mul_le_mul
  · exact pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left (abs_nonneg _) hε (le_max_left _ _)) k
  · apply le_trans _ (le_max_right 0 K)
    simpa only [Real.norm_eq_abs] using hK
      (remaining hε hT η ρ U z t, angleRatio hε hT sdev U z t x)
      ⟨⟨le_max_left _ _,ht⟩,abs_le.1 hw⟩
  · exact abs_nonneg _
  · positivity

lemma physical_algebra (κ x y A B C : ℝ) (hy : 0 < y) :
    A*((-2*y/(x^2+y^2))/y - (-2*(x^2-y^2)/(x^2+y^2)^2)) +
      B*((2*x/(x^2+y^2))/y - (x/y)*(-2*y/(x^2+y^2))/y) +
      (1/2:ℝ)*(κ/y^2*C) =
    (4*y^2/(x^2+y^2)^2)*(-A+(x/y)*(1+(x/y)^2)*B+κ/8*(1+(x/y)^2)^2*C) := by
  have hn : x^2+y^2 ≠ 0 := by positivity
  field_simp
  ring

lemma drift_nonpos {κ η : ℝ} (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η)
    (ρ : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ)
    (hy : ε ≤ (position hε hT U z t).im)
    (hU : extendDriver T U t = Real.sqrt κ*x) :
    drift hε hT (κ/2) ((8/κ-1)/2) η ρ (Real.sqrt κ) U z t x +
      (1/2:ℝ)*iteratedDeriv 2 (field hε hT (κ/2) ((8/κ-1)/2) η ρ (Real.sqrt κ) U z t) x ≤ 0 := by
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have ht := remaining_pos hε hT hη ρ U z t
  have hh : height hε hT U z t = (position hε hT U z t).im := max_eq_right hy
  rw [iteratedDeriv_eq hε hT hl hb hη, second_profile hl hb ht]
  dsimp only [drift]
  rw [variation_of_unclipped hε hT U z t hy, velocity_eq hy, hh, hU]
  simp only [Complex.div_re, Complex.div_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero, zero_mul, Complex.normSq_apply]
  simp only [neg_div, neg_sq, div_pow, Real.sq_sqrt hκ.1.le]
  have he := physical_algebra κ ((position hε hT U z t).re-Real.sqrt κ*x)
    (position hε hT U z t).im
    (profileT (κ/2) ((8/κ-1)/2) (remaining hε hT η ρ U z t) (angleRatio hε hT (Real.sqrt κ) U z t x))
    (profileW (κ/2) ((8/κ-1)/2) (remaining hε hT η ρ U z t) (angleRatio hε hT (Real.sqrt κ) U z t x))
    (profileWW (κ/2) ((8/κ-1)/2) (remaining hε hT η ρ U z t) (angleRatio hε hT (Real.sqrt κ) U z t x)) (hε.trans_le hy)
  have ha : angleRatio hε hT (Real.sqrt κ) U z t x =
      ((position hε hT U z t).re-Real.sqrt κ*x)/(position hε hT U z t).im := by
    unfold angleRatio; rw [hh]
  rw [← ha] at he
  convert (he.trans_le (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by
    have hs := profile_super hκ ht (angleRatio hε hT (Real.sqrt κ) U z t x)
    linarith))) using 1; ring

end SLEExactGauge.GammaField

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.GammaPredictable
open LoewnerCutoff LoewnerExit GammaField BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
open scoped unitInterval
variable {ε : ℝ} (hε : 0 < ε)

def coeffAt (k : ℕ) (s : ℝ≥0) (l b η sdev : ℝ) (z : ℂ) (ρ δ : ℝ)
    (q : C(I, ℝ) × ℝ) : ℝ := by
  classical
  exact if ∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg q.1 z ρ δ t then
    iteratedDeriv k (field hε s.coe_nonneg l b η ρ sdev q.1 z s) q.2 else 0

lemma coeffAt_measurable (k : ℕ) (_hk : k = 1 ∨ k = 2) (s : ℝ≥0)
    (l b η sdev : ℝ) (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (z : ℂ) (ρ δ : ℝ) :
    @Measurable (C(I, ℝ) × ℝ) ℝ (@Prod.instMeasurableSpace _ _ (borel _) inferInstance) _ (coeffAt hε k s l b η sdev z ρ δ) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hc : Continuous (fun q : C(I, ℝ) × ℝ =>
      iteratedDeriv k (field hε s.coe_nonneg l b η ρ sdev q.1 z s) q.2) := by
    have hp : Continuous (fun q : C(I, ℝ) × ℝ => ((q.1,(s:ℝ)),q.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    have hc := (continuous_derivative hε s.coe_nonneg hl hb hη ρ sdev z k).comp hp
    dsimp only [Function.comp_def] at hc
    exact hc
  apply hc.measurable.ite _ measurable_const
  exact ((isOpen_positive_on hε s.coe_nonneg z ρ δ s).preimage continuous_fst).measurableSet

def rawCoeff {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (l b η sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (sample : Ω) : ℝ :=
  if s < T then coeffAt hε k s l b η sdev z ρ δ (BrownianDriver.path B sdev s sample, B s sample) else 0

lemma rawCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (hk : k = 1 ∨ k = 2) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (l b η sdev : ℝ) (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (z : ℂ) (ρ δ : ℝ) :
    Measurable[pastSigma B s] (rawCoeff hε k B T s l b η sdev z ρ δ) := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  let : MeasurableSpace Ω := pastSigma B s
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s l b η sdev hl hb hη z ρ δ).comp
      ((BrownianDriver.path_measurable_past B sdev s).prodMk (past_measurable_eval B (s := s) le_rfl))
  · exact measurable_const

lemma rawCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (T s : ℝ≥0)
    (l b η sdev : ℝ) (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (z : ℂ) (ρ δ : ℝ) :
    AEMeasurable (rawCoeff hε k B T s l b η sdev z ρ δ) P := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s l b η sdev hl hb hη z ρ δ).comp_aemeasurable
      ((BrownianDriver.path_aemeasurable hB sdev s).prodMk (hB.toIsPreBrownianReal.hasLaw_eval s).aemeasurable)
  · exact aemeasurable_const

lemma rawCoeff_eq {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hT : 0 < (T:ℝ)) (l b η sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    rawCoeff hε k B T s l b η sdev z ρ δ sample =
      if (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ then
        iteratedDeriv k (field hε T.coe_nonneg l b η ρ sdev (BrownianDriver.path B sdev T sample) z s) (B s sample) else 0 := by
  classical
  by_cases hsT : s < T
  · have he := BrownianDriver.prefix_eq B sdev s T sample hc hsT.le
    have hf := field_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z l b η ρ sdev he
      ⟨s.coe_nonneg, le_rfl⟩
    have hd := deficit_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z ρ δ he
    have hi : (∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg (BrownianDriver.path B sdev s sample) z ρ δ t) ↔
        (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ := by
      rw [lt_stop_iff hε T.coe_nonneg hT _ z ρ δ ⟨s.coe_nonneg,hsT⟩]
      exact forall₂_congr (fun t ht => by rw [hd ht])
    simp only [rawCoeff, ite_eq_left hsT, coeffAt, hi, hf]
  · have hstop : ¬ (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ :=
      not_lt_of_ge ((stop_bounds hε T.coe_nonneg _ z ρ δ).2.trans (not_lt.1 hsT))
    simp only [rawCoeff, ite_eq_right hsT, ite_eq_right hstop]

lemma rawCoeff_stoppedCoeff_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (T : ℝ≥0)
    (hT : 0 < (T:ℝ)) (l b η sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (n i : ℕ) :
    rawCoeff hε k B T (dyadicTime T n i) l b η sdev z ρ δ =ᵐ[P]
      stoppedCoeff k B T
        (fun sample => stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ)
        (fun sample => field hε T.coe_nonneg l b η ρ sdev (BrownianDriver.path B sdev T sample) z) n i := by
  filter_upwards [hB.cont] with sample hc
  rw [rawCoeff_eq hε k B T _ hT l b η sdev z ρ δ sample hc]
  simp only [stoppedCoeff, coe_dyadicTime]

end SLEExactGauge.GammaPredictable

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.GammaField
open LoewnerCutoff LoewnerField LoewnerExit AngularBarrier
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

lemma ratio_bound {δ : ℝ} (hδ : 0 < δ) (sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ)
    (hy : ε ≤ (position hε hT U z t).im) (hs : δ ≤ sine hε hT U z t)
    (hU : extendDriver T U t = sdev*x) :
    |angleRatio hε hT sdev U z t x| ≤ 1/δ := by
  have hyp := hε.trans_le hy
  have hn : 0 < ‖position hε hT U z t - (extendDriver T U t : ℂ)‖ := by
    apply norm_pos_iff.2
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
    linarith
  have hh : δ * ‖position hε hT U z t - (extendDriver T U t : ℂ)‖ ≤ (position hε hT U z t).im := by
    apply (le_div_iff₀ hn).1
    unfold sine at hs
    rw [clampIm_eq (show ε ≤ (position hε hT U z t - (extendDriver T U t : ℂ)).im by simpa using hy)] at hs
    exact hs
  have hx := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm
    (position hε hT U z t - (extendDriver T U t : ℂ))) hδ.le
  have hxx := hx.trans hh
  simp only [Complex.sub_re, Complex.ofReal_re, hU] at hxx
  rw [angleRatio, height, max_eq_right hy, abs_div, abs_of_pos hyp]
  apply (div_le_iff₀ hyp).2
  rw [div_mul_eq_mul_div, one_mul]
  apply (le_div_iff₀ hδ).2
  nlinarith [hxx]

end SLEExactGauge.GammaField

end

end

end OAI
