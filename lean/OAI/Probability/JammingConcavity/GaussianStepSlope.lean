import Mathlib
import OAI.Probability.JammingConcavity.GaussianTwiceTerminal

namespace OAI

/-! Gaussian Step Slope. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma slope_bound_from_curvature {f : ℝ → ℝ} {D K : ℝ}
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hvals : |f 1-f 0| ≤ D)
    (hb : ∀ z, |deriv (deriv f) z| ≤ K) :
    ∀ x, |deriv f x| ≤ (D+K)*(1+|x|) := by
  obtain ⟨c,hc,he⟩ := exists_deriv_eq_slope f (show (0:ℝ)<1 by norm_num)
    hf.continuous.continuousOn hf.differentiableOn
  have hfc : |deriv f c| ≤ D := by rw [he]; simpa using hvals
  intro x
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := deriv f) (s := univ) (C := K) (fun z _ => hf' z)
    (fun z _ => by simpa only [Real.norm_eq_abs] using hb z)
    convex_univ (x := c) (y := x) (mem_univ _) (mem_univ _)
  simp only [Real.norm_eq_abs] at hh
  have hd : |x-c| ≤ 1+|x| := by
    have ht := abs_sub x c
    rw [abs_of_pos hc.1] at ht
    linarith [hc.2]
  have ht := abs_add_le (deriv f x-deriv f c) (deriv f c)
  rw [sub_add_cancel] at ht
  have hm := mul_le_mul_of_nonneg_left hd hK
  nlinarith [mul_nonneg hD (abs_nonneg x)]

theorem gaussian_step_slope : GaussianStepSlopeStatement := by
  intro A B C κ Q hQ hA hC hk hsub
  let K := C+κ/(1-κ*Q)
  let D := 2*|B|+A*(3+2*Q)
  have hden : 0 < 1-κ*Q := by linarith
  have hK : 0 ≤ K := add_nonneg hC (div_nonneg hk hden.le)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D+K,add_nonneg hD hK,?_⟩
  intro u hu rs hrs hsum
  obtain ⟨hf,hf',hb⟩ := gaussian_step_bounds u A B C κ Q hQ hu rs hrs hsum
  have hR := gaussianStepTime_nonneg (fun r hr => (hrs r hr).2.2)
  have hdenR : 0 < 1-κ*gaussianStepTime rs := by
    have hh := mul_le_mul_of_nonneg_left hsum hk
    linarith
  have hcap : κ/(1-κ*gaussianStepTime rs) ≤ κ/(1-κ*Q) :=
    div_le_div_of_nonneg_left hk hden (by nlinarith [mul_le_mul_of_nonneg_left hsum hk])
  have hcurv (z : ℝ) : |deriv (deriv (gaussianRowComposition rs u)) z| ≤ K := by
    rw [abs_le]
    have hz := (hb z).2
    dsimp [K]
    constructor <;> linarith [div_nonneg hk hden.le,hz.1,hz.2]
  have habs (z : ℝ) : |gaussianRowComposition rs u z| ≤ |B|+A*(1+z^2+Q) := by
    rw [abs_le]
    have hz := (hb z).1
    have hadd := mul_le_mul_of_nonneg_left hsum hA
    have hp : 0 ≤ A*(1+z^2+Q) := mul_nonneg hA (by positivity)
    constructor <;> nlinarith [abs_nonneg B,le_abs_self B]
  have hv : |gaussianRowComposition rs u 1-gaussianRowComposition rs u 0| ≤ D := by
    have hh := abs_sub (gaussianRowComposition rs u 1) (gaussianRowComposition rs u 0)
    have h1 := habs 1
    have h0 := habs 0
    dsimp [D]
    norm_num at h1 h0
    linarith
  exact slope_bound_from_curvature hf hf' hD hK hv hcurv
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma heat_affine_continuousAt {v : ℝ → ℝ} (hv : Continuous v)
    (hg : HeatQuadraticGrowth v) {a b : ℝ → ℝ} {t₀ : ℝ}
    (ha : ContinuousAt a t₀) (hb : ContinuousAt b t₀) :
    ContinuousAt (fun t => ∫ z : ℝ, v (a t+b t*z) ∂gaussianReal 0 1) t₀ := by
  let K := 1+|a t₀|+|b t₀|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hea : ∀ᶠ t in 𝓝 t₀, |a t| ≤ K :=
    (ha.abs.tendsto.eventually (eventually_lt_nhds (show |a t₀| < K by
      dsimp [K]; linarith [abs_nonneg (b t₀)]))).mono fun _ h => h.le
  have heb : ∀ᶠ t in 𝓝 t₀, |b t| ≤ K :=
    (hb.abs.tendsto.eventually (eventually_lt_nhds (show |b t₀| < K by
      dsimp [K]; linarith [abs_nonneg (a t₀)]))).mono fun _ h => h.le
  obtain ⟨C,hC,hgrow⟩ := hg
  refine continuousAt_of_dominated
    (μ := gaussianReal 0 1) (bound := fun z => C*(1+2*K)^2*(1+|z|)^2)
    (Eventually.of_forall fun t => (hv.measurable.comp (by fun_prop)).aestronglyMeasurable)
    ?_ ((gaussian_abs_one_pow_integrable 2).const_mul _) ?_
  · filter_upwards [hea,heb] with t hat hbt
    filter_upwards [] with z
    have hab : 1+|a t+b t*z| ≤ (1+2*K)*(1+|z|) :=
      (heat_affine_bound (a t) (b t) z).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    rw [Real.norm_eq_abs]
    calc
      |v (a t+b t*z)| ≤ C*(1+|a t+b t*z|)^2 := hgrow _
      _ ≤ C*((1+2*K)*(1+|z|))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hab 2) hC
      _ = _ := by ring
  · filter_upwards [] with z
    exact hv.continuousAt.comp (ha.add (hb.mul_const z))

lemma gaussianHeat_time_continuous {v : ℝ → ℝ} (hv : Continuous v)
    (hg : HeatQuadraticGrowth v) (x : ℝ) :
    Continuous (fun T => gaussianHeat v T x) := by
  rw [continuous_iff_continuousAt]
  intro T
  exact heat_affine_continuousAt hv hg continuousAt_const Real.continuous_sqrt.continuousAt

lemma gaussianRowOperator_time_continuous {u : ℝ → ℝ} {A B C κ Q a : ℝ}
    (hu : Twice.RowTwiceTerminal u A B C κ Q) (ha : 0 ≤ a) (x : ℝ) :
    Continuous (fun T => gaussianRowOperator a T u x) := by
  by_cases haz : a=0
  · subst a
    simpa [gaussianRowOperator] using gaussianHeat_time_continuous
      hu.differentiable.continuous (Twice.row_terminal_quadratic_growth hu) x
  · have he : Continuous (fun y => Real.exp (a*u y)) := by
      exact Real.continuous_exp.comp (continuous_const.mul hu.differentiable.continuous)
    have hg := (Twice.row_exp_growth hu ha).1
    have ht := gaussianHeat_time_continuous he hg x
    have hp (T : ℝ) : gaussianHeat (fun y => Real.exp (a*u y)) T x ≠ 0 :=
      (integral_exp_pos (heat_affine_quadratic_integrable he.measurable hg x (Real.sqrt T))).ne'
    simpa [gaussianRowOperator,haz] using (ht.log hp).const_mul (1/a)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma abs_sub_le_of_hasDerivAt_Ioo {f f' : ℝ → ℝ} {s t D : ℝ}
    (hst : s < t) (hc : ContinuousOn f (Icc s t))
    (hd : ∀ r ∈ Ioo s t, HasDerivAt f (f' r) r)
    (hb : ∀ r ∈ Ioo s t, |f' r| ≤ D) : |f t-f s| ≤ D*(t-s) := by
  obtain ⟨r,hr,he⟩ := exists_hasDerivAt_eq_slope f f' hst hc hd
  have hh := hb r hr
  rw [he,abs_div,abs_of_pos (sub_pos.mpr hst)] at hh
  exact (div_le_iff₀ (sub_pos.mpr hst)).mp hh

theorem gaussian_step_time : GaussianStepTimeStatement := by
  intro A B C κ Q hQ hA hC hk hsub
  obtain ⟨L,hL,hlin⟩ := gaussian_step_slope A B C κ Q hQ hA hC hk hsub
  let K := C+κ/(1-κ*Q)
  have hden : 0 < 1-κ*Q := by linarith
  have hK : 0 ≤ K := add_nonneg hC (div_nonneg hk hden.le)
  refine ⟨K+2*L^2,by positivity,?_⟩
  intro u hu rs hrs a s t ha ha1 hs ht htime x
  have hR := gaussianStepTime_nonneg (fun r hr => (hrs r hr).2.2)
  have hRQ : gaussianStepTime rs ≤ Q := by
    have hm : 0 ≤ max s t := hs.trans (le_max_left _ _)
    linarith
  obtain ⟨hdf,hdf',hbf⟩ := gaussian_step_bounds u A B C κ Q hQ hu rs hrs hRQ
  have hsum : κ*((Q-gaussianStepTime rs)+gaussianStepTime rs)<1 := by simpa using hsub
  obtain ⟨hkn,hknQ,_⟩ := gaussian_curvature_update hk hR (sub_nonneg.mpr hRQ) hsum
  have htw : Twice.RowTwiceTerminal (gaussianRowComposition rs u)
      (A*(1+gaussianStepTime rs)) B C (κ/(1-κ*gaussianStepTime rs))
      (Q-gaussianStepTime rs) := by
    refine ⟨hdf,hdf',mul_nonneg hA (by linarith),hC,hkn,hknQ,fun y => ?_⟩
    refine ⟨?_,(hbf y).1.2,(hbf y).2⟩
    have hh := (hbf y).1.1
    nlinarith [mul_nonneg (mul_nonneg hA hR) (sq_nonneg y)]
  let f : ℝ → ℝ := fun r => gaussianRowOperator a r (gaussianRowComposition rs u) x
  let d : ℝ → ℝ := fun r => (1/2:ℝ)*
    (deriv (deriv (gaussianRowOperator a r (gaussianRowComposition rs u))) x+
      a*(deriv (gaussianRowOperator a r (gaussianRowComposition rs u)) x)^2)
  have hcont : Continuous f := gaussianRowOperator_time_continuous htw ha x
  have hdiff (r : ℝ) (hr : 0 < r) : HasDerivAt f (d r) r :=
    (Twice.gaussianRowOperator_calculus htw ha hr).2.2 x
  have hb (r : ℝ) (hr : 0 ≤ r) (hrQ : r+gaussianStepTime rs ≤ Q) :
      |d r| ≤ (K+2*L^2)*(1+x^2) := by
    have hrr : ∀ v ∈ (a,r)::rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · subst v; exact ⟨ha,ha1,hr⟩
      · exact hrs v h
    have htot : gaussianStepTime ((a,r)::rs) ≤ Q := by
      simpa [gaussianStepTime] using hrQ
    obtain ⟨_,_,hbb⟩ := gaussian_step_bounds u A B C κ Q hQ hu ((a,r)::rs) hrr htot
    have hj := hlin u hu ((a,r)::rs) hrr htot x
    have hdenr : 0 < 1-κ*gaussianStepTime ((a,r)::rs) := by
      have hh := mul_le_mul_of_nonneg_left htot hk
      linarith
    have hcap : κ/(1-κ*gaussianStepTime ((a,r)::rs)) ≤ κ/(1-κ*Q) :=
      div_le_div_of_nonneg_left hk hden (by nlinarith [mul_le_mul_of_nonneg_left htot hk])
    have hcurv : |deriv (deriv (gaussianRowOperator a r (gaussianRowComposition rs u))) x| ≤ K := by
      rw [abs_le]
      have hh := (hbb x).2
      change -C ≤ deriv (deriv (gaussianRowOperator a r (gaussianRowComposition rs u))) x ∧
        deriv (deriv (gaussianRowOperator a r (gaussianRowComposition rs u))) x ≤
          κ/(1-κ*gaussianStepTime ((a,r)::rs)) at hh
      dsimp [K]
      constructor <;> linarith [hh.1,hh.2,div_nonneg hk hden.le]
    change |deriv (gaussianRowOperator a r (gaussianRowComposition rs u)) x| ≤ L*(1+|x|) at hj
    have hsq : (deriv (gaussianRowOperator a r (gaussianRowComposition rs u)) x)^2 ≤
        2*L^2*(1+x^2) := by
      have hp := pow_le_pow_left₀ (abs_nonneg _) hj 2
      rw [sq_abs] at hp
      have hx : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
      have hx' := mul_le_mul_of_nonneg_left hx (sq_nonneg L)
      nlinarith [sq_nonneg L]
    have hadd := abs_add_le
      (deriv (deriv (gaussianRowOperator a r (gaussianRowComposition rs u))) x)
      (a*(deriv (gaussianRowOperator a r (gaussianRowComposition rs u)) x)^2)
    rw [abs_of_nonneg (mul_nonneg ha (sq_nonneg _))] at hadd
    have haSq := mul_le_mul_of_nonneg_right ha1
      (sq_nonneg (deriv (gaussianRowOperator a r (gaussianRowComposition rs u)) x))
    dsimp [d]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    nlinarith [mul_nonneg hK (sq_nonneg x)]
  have hbound (s t : ℝ) (hs : 0 ≤ s) (hst : s<t)
      (hT : t+gaussianStepTime rs ≤ Q) :
      |f t-f s| ≤ (K+2*L^2)*(1+x^2)*(t-s) := by
    apply abs_sub_le_of_hasDerivAt_Ioo hst hcont.continuousOn
      (fun r hr => hdiff r (by linarith [hr.1]))
    intro r hr
    exact hb r (by linarith [hr.1]) (by linarith [hr.2])
  rcases lt_trichotomy s t with hst | he | hts
  · rw [abs_of_pos (sub_pos.mpr hst)]
    exact hbound s t hs hst (by linarith [le_max_right s t])
  · subst t
    simp
  · rw [abs_sub_comm t s,abs_of_pos (sub_pos.mpr hts)]
    rw [abs_sub_comm (gaussianRowOperator a t (gaussianRowComposition rs u) x)]
    exact hbound t s ht hts (by linarith [le_max_left s t])
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace MicroscopicJamming

lemma gaussianStepPath_time_bound {A B C κ Q D : ℝ} {u : ℝ → ℝ}
    (_hQ : 0 < Q) (_hu : RowAnalyticTerminal u A B C κ Q) (hD : 0 ≤ D)
    (hblock : ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
      ∀ a s t : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ s → 0 ≤ t →
      max s t+gaussianStepTime rs ≤ Q → ∀ x,
      |gaussianRowOperator a t (gaussianRowComposition rs u) x-
        gaussianRowOperator a s (gaussianRowComposition rs u) x| ≤ D*(1+x^2)*|t-s|) :
    ∀ rs : List (ℝ × ℝ), (∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
      gaussianStepTime rs ≤ Q → ∀ s t, 0 ≤ s → s ≤ t → ∀ x,
      |gaussianStepPath rs u t x-gaussianStepPath rs u s x| ≤ D*(1+x^2)*(t-s) := by
  intro rs
  induction rs with
  | nil =>
    intro _ _ s t hs hst x
    simp only [gaussianStepPath,gaussianStepRemainder,gaussianRowComposition,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg hD (by positivity)) (sub_nonneg.mpr hst)
  | cons r rs ih =>
    intro hrs hsum s t hs hst x
    have hr := hrs r (by simp)
    have htail : ∀ v ∈ rs, 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    have hR := gaussianStepTime_nonneg (fun v hv => (htail v hv).2.2)
    have htot : gaussianStepTime (r::rs)=r.2+gaussianStepTime rs := by simp [gaussianStepTime]
    rw [htot] at hsum
    have ht : 0 ≤ t := hs.trans hst
    by_cases htR : t ≤ r.2
    · have hsR : s ≤ r.2 := hst.trans htR
      rw [gaussianStepPath_cons_le r rs u htR,gaussianStepPath_cons_le r rs u hsR]
      have hm : max (r.2-s) (r.2-t)+gaussianStepTime rs ≤ Q := by
        rw [max_eq_left (by linarith)]
        linarith
      have hh := hblock rs htail r.1 (r.2-s) (r.2-t) hr.1 hr.2.1
        (sub_nonneg.mpr hsR) (sub_nonneg.mpr htR) hm x
      have he : |(r.2-t)-(r.2-s)|=t-s := by rw [abs_of_nonpos (by linarith)]; ring
      simpa only [he] using hh
    · have hRt : r.2 < t := lt_of_not_ge htR
      rw [gaussianStepPath_cons_gt r rs u hRt]
      by_cases hsR : s ≤ r.2
      · rw [gaussianStepPath_cons_le r rs u hsR]
        have htailQ : gaussianStepTime rs ≤ Q := by linarith
        have hfirst := ih htail htailQ 0 (t-r.2) (by norm_num) (by linarith) x
        rw [gaussianStepPath_zero (fun v hv => (htail v hv).2.2) u] at hfirst
        have hsecond := hblock rs htail r.1 (r.2-s) 0 hr.1 hr.2.1
          (sub_nonneg.mpr hsR) (by norm_num) (by rw [max_eq_left (by linarith)]; linarith) x
        rw [gaussianRowOperator_zero] at hsecond
        rw [abs_of_nonpos (by linarith : 0-(r.2-s) ≤ 0)] at hsecond
        have htri := abs_sub_le (gaussianStepPath rs u (t-r.2) x)
          (gaussianRowComposition rs u x) (gaussianRowOperator r.1 (r.2-s) (gaussianRowComposition rs u) x)
        nlinarith
      · rw [gaussianStepPath_cons_gt r rs u (lt_of_not_ge hsR)]
        have hh := ih htail (by linarith) (s-r.2) (t-r.2) (by linarith) (by linarith) x
        convert hh using 1; ring

theorem gaussian_step_path : GaussianStepPathStatement := by
  intro A B C κ Q hQ hA hC hk hsub
  obtain ⟨D,hD,hblock⟩ := gaussian_step_time A B C κ Q hQ hA hC hk hsub
  obtain ⟨L,hL,hlin⟩ := gaussian_step_slope A B C κ Q hQ hA hC hk hsub
  refine ⟨D,L,hD,hL,?_⟩
  intro u hu rs hrs hsum
  have hnonneg : ∀ r ∈ rs, 0 ≤ r.2 := fun r hr => (hrs r hr).2.2
  refine ⟨fun x => congrFun (gaussianStepPath_zero hnonneg u) x,
    fun x => congrFun (gaussianStepPath_terminal hrs u) x,?_,?_⟩
  · intro s t hs ht x
    rcases le_total s t with hst | hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact gaussianStepPath_time_bound hQ hu hD (hblock u hu) rs hrs hsum s t hs hst x
    · rw [abs_sub_comm t s,abs_of_nonneg (sub_nonneg.mpr hts),abs_sub_comm]
      exact gaussianStepPath_time_bound hQ hu hD (hblock u hu) rs hrs hsum t s ht hts x
  · intro t ht htR
    obtain ⟨hv,hvT⟩ := gaussianStepRemainder_valid hrs ht
    rw [max_eq_left (sub_nonneg.mpr htR)] at hvT
    have hvQ : gaussianStepTime (gaussianStepRemainder rs t) ≤ Q := by rw [hvT]; linarith
    obtain ⟨hdf,hdf',hbf⟩ := gaussian_step_bounds u A B C κ Q hQ hu _ hv hvQ
    refine ⟨hdf,hdf',fun x => ⟨hlin u hu _ hv hvQ x,(hbf x).2.1,?_⟩⟩
    change deriv (deriv (gaussianRowComposition (gaussianStepRemainder rs t) u)) x ≤ _
    rw [← hvT]
    exact (hbf x).2.2
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace MicroscopicJamming

lemma gaussianStepPath_cylinder_lipschitz {u : ℝ → ℝ} {rs : List (ℝ × ℝ)}
    {Q R D L : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hQeq : gaussianStepTime rs=Q)
    (htime : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x,
      |gaussianStepPath rs u t x-gaussianStepPath rs u s x| ≤ D*(1+x^2)*|t-s|)
    (hspace : ∀ t, 0 ≤ t → t ≤ gaussianStepTime rs →
      Differentiable ℝ (gaussianStepPath rs u t) ∧
      ∀ x, |deriv (gaussianStepPath rs u t) x| ≤ L*(1+|x|)) :
    LipschitzWith (⟨D*(1+R^2)+L*(1+R),by positivity⟩ : ℝ≥0)
      (fun p : RowCylinder Q R => gaussianStepPath rs u p.1.1 p.1.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hp := p.2
  have hq := q.2
  have hpx : |p.1.2| ≤ R := abs_le.mpr hp.2
  have hqx : |q.1.2| ≤ R := abs_le.mpr hq.2
  have hhT := htime q.1.1 p.1.1 hq.1.1 hp.1.1 p.1.2
  have hhS := hspace q.1.1 hq.1.1 (by rw [hQeq]; exact hq.1.2)
  have hhx : |gaussianStepPath rs u q.1.1 p.1.2-gaussianStepPath rs u q.1.1 q.1.2| ≤
      L*(1+R)*|p.1.2-q.1.2| := by
    have hc := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := gaussianStepPath rs u q.1.1) (s := Icc (-R) R) (C := L*(1+R))
      (fun z _ => hhS.1 z)
      (fun z hz => by
        rw [Real.norm_eq_abs]
        exact (hhS.2 z).trans (mul_le_mul_of_nonneg_left (by linarith [abs_le.mpr hz]) hL))
      (convex_Icc (-R) R) hq.2 hp.2
    simpa only [Real.norm_eq_abs] using hc
  have hprodT : |p.1.1-q.1.1| ≤ dist p q := by
    change dist (p.1.1) (q.1.1) ≤ dist p q
    change dist p.1.1 q.1.1 ≤ dist p.1 q.1
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hprodX : |p.1.2-q.1.2| ≤ dist p q := by
    change dist (p.1.2) (q.1.2) ≤ dist p q
    change dist p.1.2 q.1.2 ≤ dist p.1 q.1
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hp2 : p.1.2^2 ≤ R^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg p.1.2) hR).mpr hpx
    simpa only [sq_abs] using hh
  have hhT' : |gaussianStepPath rs u p.1.1 p.1.2-gaussianStepPath rs u q.1.1 p.1.2| ≤
      D*(1+R^2)*dist p q := hhT.trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hD) hprodT (abs_nonneg _) (by positivity))
  have hhS' := hhx.trans (mul_le_mul_of_nonneg_left hprodX (by positivity : 0 ≤ L*(1+R)))
  have htri := abs_sub_le (gaussianStepPath rs u p.1.1 p.1.2)
    (gaussianStepPath rs u q.1.1 p.1.2) (gaussianStepPath rs u q.1.1 q.1.2)
  change |gaussianStepPath rs u p.1.1 p.1.2-gaussianStepPath rs u q.1.1 q.1.2| ≤
    (D*(1+R^2)+L*(1+R))*dist p q
  nlinarith

lemma gaussianStepPath_cylinder_bound {u : ℝ → ℝ} {A B C κ Q R : ℝ}
    (hQ : 0 < Q) (hR : 0 ≤ R) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hQeq : gaussianStepTime rs=Q) (p : RowCylinder Q R) :
    |gaussianStepPath rs u p.1.1 p.1.2| ≤ |B|+A*(1+R^2+Q) := by
  obtain ⟨hv,hvT⟩ := gaussianStepRemainder_valid hrs p.2.1.1
  rw [hQeq,max_eq_left (sub_nonneg.mpr p.2.1.2)] at hvT
  have hvQ : gaussianStepTime (gaussianStepRemainder rs p.1.1) ≤ Q := by rw [hvT]; linarith [p.2.1.1]
  have hb := (gaussian_step_bounds u A B C κ Q hQ hu _ hv hvQ).2.2 p.1.2
  change (-A*(1+p.1.2^2+gaussianStepTime (gaussianStepRemainder rs p.1.1)) ≤
    gaussianStepPath rs u p.1.1 p.1.2 ∧ gaussianStepPath rs u p.1.1 p.1.2 ≤ B) ∧ _ at hb
  have hp := abs_le.mpr p.2.2
  have hp2 : p.1.2^2 ≤ R^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg p.1.2) hR).mpr hp
    simpa only [sq_abs] using hh
  have hmul := mul_le_mul_of_nonneg_left (show 1+p.1.2^2+gaussianStepTime (gaussianStepRemainder rs p.1.1) ≤
    1+R^2+Q by linarith) hu.2.1
  rw [abs_le]
  have hnn : 0 ≤ A*(1+R^2+Q) := mul_nonneg hu.2.1 (by positivity)
  constructor <;> linarith [hb.1.1,hb.1.2,abs_nonneg B,le_abs_self B]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace MicroscopicJamming

lemma gaussianStepPath_jointly_continuous {u : ℝ → ℝ} {rs : List (ℝ × ℝ)}
    {Q D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (hQeq : gaussianStepTime rs=Q)
    (htime : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x,
      |gaussianStepPath rs u t x-gaussianStepPath rs u s x| ≤ D*(1+x^2)*|t-s|)
    (hspace : ∀ t, 0 ≤ t → t ≤ gaussianStepTime rs →
      Differentiable ℝ (gaussianStepPath rs u t) ∧
      ∀ x, |deriv (gaussianStepPath rs u t) x| ≤ L*(1+|x|)) :
    ContinuousOn (fun p : ℝ × ℝ => gaussianStepPath rs u p.1 p.2) (Icc 0 Q ×ˢ univ) := by
  intro p hp
  let R := |p.2|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hxl : -R < p.2 := by dsimp [R]; linarith [neg_abs_le p.2]
  have hxr : p.2 < R := by dsimp [R]; linarith [le_abs_self p.2]
  have hc : ContinuousOn (fun p : ℝ × ℝ => gaussianStepPath rs u p.1 p.2)
      (Icc 0 Q ×ˢ Icc (-R) R) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (gaussianStepPath_cylinder_lipschitz hR.le hD hL hQeq htime hspace).continuous
  apply (hc p ⟨hp.1,⟨hxl.le,hxr.le⟩⟩).mono_of_mem_nhdsWithin
  have hh : ∀ᶠ q : ℝ × ℝ in 𝓝 p, q.2 ∈ Icc (-R) R :=
    continuous_snd.continuousAt.eventually (Icc_mem_nhds hxl hxr)
  filter_upwards [self_mem_nhdsWithin,hh.filter_mono nhdsWithin_le_nhds] with q hq hqx
  exact ⟨hq.1,hqx⟩

lemma gaussianStepPath_global_value_bound {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hQeq : gaussianStepTime rs=Q) {t : ℝ} (ht : t ∈ Icc 0 Q) (x : ℝ) :
    |gaussianStepPath rs u t x| ≤ (|B|+A*(1+Q))*(1+x^2) := by
  have hx : x ∈ Icc (-|x|) |x| := abs_le.mp le_rfl
  have hh := gaussianStepPath_cylinder_bound hQ (abs_nonneg x) hu hrs hQeq
    (⟨(t,x),ht,hx⟩ : RowCylinder Q |x|)
  change |gaussianStepPath rs u t x| ≤ |B|+A*(1+|x|^2+Q) at hh
  rw [sq_abs] at hh
  have h1 := mul_nonneg (abs_nonneg B) (sq_nonneg x)
  have h2 := mul_nonneg (mul_nonneg hu.2.1 hQ.le) (sq_nonneg x)
  nlinarith
end MicroscopicJamming

 
 

namespace MicroscopicJamming

def GaussianStepPDEStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q : ℝ), 0 < Q → RowAnalyticTerminal u A B C κ Q →
  ∀ (pre rs : List (ℝ × ℝ)) (a T : ℝ),
    (∀ r ∈ pre ++ (a,T)::rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
    gaussianStepTime (pre ++ (a,T)::rs) ≤ Q →
    ∀ t : ℝ, 0 < t → t < T → ∀ x,
      HasDerivAt (fun s => gaussianStepPath (pre ++ (a,T)::rs) u (gaussianStepTime pre+s) x)
        (-(1/2:ℝ)*(deriv (deriv (gaussianStepPath (pre ++ (a,T)::rs) u
          (gaussianStepTime pre+t))) x+
          a*(deriv (gaussianStepPath (pre ++ (a,T)::rs) u
          (gaussianStepTime pre+t)) x)^2)) t
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma gaussian_composition_twice {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0 < Q) (hu : RowAnalyticTerminal u A B C κ Q)
    {rs : List (ℝ × ℝ)} (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hsum : gaussianStepTime rs ≤ Q) :
    Twice.RowTwiceTerminal (gaussianRowComposition rs u)
      (A*(1+gaussianStepTime rs)) B C (κ/(1-κ*gaussianStepTime rs))
      (Q-gaussianStepTime rs) := by
  obtain ⟨hd,hd',hb⟩ := gaussian_step_bounds u A B C κ Q hQ hu rs hrs hsum
  have hR := gaussianStepTime_nonneg (fun r hr => (hrs r hr).2.2)
  have hk := hu.2.2.2.1
  have hsub : κ*((Q-gaussianStepTime rs)+gaussianStepTime rs)<1 := by
    simpa using hu.2.2.2.2.1
  obtain ⟨hkn,hknQ,_⟩ := gaussian_curvature_update hk hR (sub_nonneg.mpr hsum) hsub
  refine ⟨hd,hd',mul_nonneg hu.2.1 (by linarith),hu.2.2.1,hkn,hknQ,fun y => ?_⟩
  refine ⟨?_,(hb y).1.2,(hb y).2⟩
  have hh := (hb y).1.1
  nlinarith [mul_nonneg (mul_nonneg hu.2.1 hR) (sq_nonneg y)]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma gaussianStepTime_append (pre rs : List (ℝ × ℝ)) :
    gaussianStepTime (pre++rs)=gaussianStepTime pre+gaussianStepTime rs := by
  simp [gaussianStepTime]

lemma gaussianStepPath_prefix (pre rs : List (ℝ × ℝ))
    (hp : ∀ r ∈ pre, 0 ≤ r.2) (u : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    gaussianStepPath (pre++rs) u (gaussianStepTime pre+t)=gaussianStepPath rs u t := by
  induction pre with
  | nil => simp [gaussianStepTime]
  | cons r pre ih =>
    have hr := hp r (by simp)
    have htail : ∀ v ∈ pre, 0 ≤ v.2 := fun v hv => hp v (by simp [hv])
    have hP := gaussianStepTime_nonneg htail
    have hsum : gaussianStepTime (r::pre)=r.2+gaussianStepTime pre := by simp [gaussianStepTime]
    simp only [List.cons_append,hsum]
    rw [gaussianStepPath_cons_gt r (pre++rs) u (by linarith)]
    have he : r.2+gaussianStepTime pre+t-r.2=gaussianStepTime pre+t := by ring
    rw [he]
    exact ih htail

theorem gaussian_step_pde : GaussianStepPDEStatement := by
  intro u A B C κ Q hQ hu pre rs a T hrs hsum t ht htT x
  have hr : 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ T := hrs (a,T) (by simp)
  have hpre : ∀ r ∈ pre, 0 ≤ r.2 := fun r h => (hrs r (List.mem_append_left _ h)).2.2
  have htail : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := fun r h =>
    hrs r (List.mem_append_right _ (by simp [h]))
  have hP := gaussianStepTime_nonneg hpre
  have htime : gaussianStepTime (pre++(a,T)::rs)=gaussianStepTime pre+T+gaussianStepTime rs := by
    rw [gaussianStepTime_append]
    simp [gaussianStepTime,add_assoc]
  have hR : gaussianStepTime rs ≤ Q := by rw [htime] at hsum; linarith
  have htw := gaussian_composition_twice hQ hu htail hR
  have hd := (Twice.gaussianRowOperator_calculus htw hr.1 (sub_pos.mpr htT)).2.2 x
  have hc := hd.comp t ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have hpath (s : ℝ) (hs : 0 < s) (hsT : s < T) :
      gaussianStepPath (pre++(a,T)::rs) u (gaussianStepTime pre+s)=
        gaussianRowOperator a (T-s) (gaussianRowComposition rs u) := by
    rw [gaussianStepPath_prefix pre ((a,T)::rs) hpre u hs]
    exact gaussianStepPath_cons_le (a,T) rs u hsT.le
  have hh := hc.congr_of_eventuallyEq
    (show (fun s => gaussianStepPath (pre++(a,T)::rs) u (gaussianStepTime pre+s) x) =ᶠ[𝓝 t]
      (fun s => gaussianRowOperator a (T-s) (gaussianRowComposition rs u) x) from by
      filter_upwards [eventually_gt_nhds ht,eventually_lt_nhds htT] with s hs hsT
      exact congrFun (hpath s hs hsT) x)
  rw [hpath t ht htT]
  simpa only [zero_sub,mul_neg_one,neg_mul] using hh
end MicroscopicJamming

 
 

open Set Filter
open scoped Topology

namespace MicroscopicJamming

def gaussianStepCoefficient : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (a,T)::rs,t => if t ≤ T then a else gaussianStepCoefficient rs (t-T)

 

def RowClassicalVarianceSolution (Q : ℝ) (u m : ℝ → ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc 0 Q ×ˢ univ) ∧
  ContinuousOn (fun p : ℝ × ℝ => deriv (F p.1) p.2) (Icc 0 Q ×ˢ univ) ∧
  ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (F p.1)) p.2) (Icc 0 Q ×ˢ univ) ∧
  (∀ t ∈ Icc 0 Q, Differentiable ℝ (F t) ∧ Differentiable ℝ (deriv (F t))) ∧
  (∀ t ∈ Ioo 0 Q, ∀ x, HasDerivAt (fun r => F r x)
    (-(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)) t) ∧
  (∀ x, F Q x=u x) ∧
  ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 Q, ∀ x,
    |F t x| ≤ K*(1+x^2) ∧ |deriv (F t) x| ≤ K*(1+|x|)

 

def RowVarianceExistenceStatement : Prop :=
  ∀ A B C κ Q : ℝ, 0 < Q → 0 ≤ A → 0 ≤ C → 0 ≤ κ → κ*Q < 1 →
  ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ → ℝ, RowAnalyticTerminal u A B C κ Q →
  ∀ m : ℝ → ℝ, ContinuousOn m (Icc 0 Q) → (∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1) →
  ∃ F : ℝ → ℝ → ℝ, RowClassicalVarianceSolution Q u m F ∧
    (∀ t ∈ Icc 0 Q, ∀ x, -A*(1+x^2+Q-t) ≤ F t x ∧ F t x ≤ B ∧
      |deriv (F t) x| ≤ L*(1+|x|) ∧
      -C ≤ deriv (deriv (F t)) x ∧ deriv (deriv (F t)) x ≤ κ/(1-κ*(Q-t))) ∧
    (∀ G : ℝ → ℝ → ℝ, RowClassicalVarianceSolution Q u m G →
      ∀ t ∈ Icc 0 Q, ∀ x, F t x=G t x) ∧
    (∀ rs : ℕ → List (ℝ × ℝ),
      (∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) →
      (∀ n, gaussianStepTime (rs n)=Q) →
      TendstoUniformlyOn (fun n => gaussianStepCoefficient (rs n)) m atTop (Icc 0 Q) →
      ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => gaussianStepPath (rs n) u p.1 p.2)
        (fun p => F p.1 p.2) atTop (Icc 0 Q ×ˢ Icc (-R) R))
end MicroscopicJamming

end

end OAI
