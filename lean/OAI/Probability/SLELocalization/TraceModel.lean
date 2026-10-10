import Mathlib
import OAI.Probability.SLELocalization.SobolevMeans
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Boundary Cutoff estimates. -/

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.BoundaryCutoff

lemma norm_velocity_sub_le {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε)
    (u : ℝ) (z w : ℂ) : ‖velocity σ ε u z-velocity σ ε u w‖ ≤ (4/ε^2)*‖z-w‖ := by
  let a := clamp σ ε (z-(u:ℂ))
  let b := clamp σ ε (w-(u:ℂ))
  have ha : a ≠ 0 := clamp_ne_zero hσ hε _
  have hb : b ≠ 0 := clamp_ne_zero hσ hε _
  have hd : ε^2 ≤ ‖a*b‖ := by
    rw [norm_mul,pow_two]
    exact mul_le_mul (clamp_norm hσ hε _) (clamp_norm hσ hε _) hε.le (norm_nonneg _)
  have he : velocity σ ε u z-velocity σ ε u w = 2*(b-a)/(a*b) := by
    change 2/a-2/b=2*(b-a)/(a*b)
    field_simp
  rw [he,norm_div,norm_mul,Complex.norm_ofNat]
  have hn : ‖b-a‖ ≤ 2*‖z-w‖ := by
    simpa only [a,b,norm_sub_rev,sub_sub_sub_cancel_right] using
      clamp_norm_sub (ε:=ε) hσ (z-(u:ℂ)) (w-(u:ℂ))
  calc
    2*‖b-a‖/‖a*b‖ ≤ (2*(2*‖z-w‖))/ε^2 :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hn (by norm_num))
        (sq_pos_of_pos hε) hd
    _ = (4/ε^2)*‖z-w‖ := by ring

lemma velocity_lipschitz {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε) (u : ℝ) :
    LipschitzWith ⟨4/ε^2,by positivity⟩ (velocity σ ε u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  exact norm_velocity_sub_le hσ hε u z w

lemma continuous_velocity {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℂ => velocity σ ε p.1 p.2) := by
  unfold velocity clamp
  refine continuous_const.div ?_ (fun p => clamp_ne_zero hσ hε _)
  change Continuous (fun p : ℝ × ℂ => Complex.equivRealProdCLM.symm
    (σ*max (σ*(p.2-(p.1:ℂ)).re) ε,(p.2-(p.1:ℂ)).im))
  apply Complex.equivRealProdCLM.symm.continuous.comp
  apply Continuous.prodMk <;> fun_prop

lemma exists_solution {σ ε T : ℝ} (hσ : |σ| = 1) (hε : 0 < ε) (hT : 0 ≤ T)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Icc 0 T)) (z : ℂ) :
    ∃ H : ℝ → ℂ, H 0 = z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Icc 0 T) t := by
  let L : ℝ≥0 := ⟨2/ε,by positivity⟩
  let K : ℝ≥0 := ⟨4/ε^2,by positivity⟩
  let a : ℝ≥0 := ⟨(2/ε)*T,mul_nonneg (by positivity) hT⟩
  have hp : IsPicardLindelof (fun t => velocity σ ε (U t)) ⟨0,⟨le_rfl,hT⟩⟩ z a 0 L K := by
    constructor
    · exact fun t _ => (velocity_lipschitz hσ hε (U t)).lipschitzOnWith
    · intro w _
      have hc : ContinuousOn (fun t : ℝ => (U t,w)) (Icc 0 T) :=
        hU.prodMk continuousOn_const
      simpa only [Function.comp_def] using (continuous_velocity hσ hε).comp_continuousOn hc
    · exact fun t _ w _ => norm_velocity_le hσ hε (U t) w
    · dsimp [L,a]
      simp only [sub_zero,sub_self,max_eq_left hT]
      rfl
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma norm_velocity_driver_sub_le {σ ε : ℝ} (hσ : |σ| = 1) (hε : 0 < ε)
    (u v : ℝ) (z : ℂ) : ‖velocity σ ε u z-velocity σ ε v z‖ ≤ (4/ε^2)*|u-v| := by
  have he (a : ℝ) : velocity σ ε 0 (z-(a:ℂ)) = velocity σ ε a z := by simp [velocity]
  have hh := norm_velocity_sub_le hσ hε 0 (z-(u:ℂ)) (z-(v:ℂ))
  rw [he,he] at hh
  convert hh using 1
  rw [sub_sub_sub_cancel_left,← Complex.ofReal_sub,Complex.norm_real,abs_sub_comm]
  simp [Real.norm_eq_abs]

lemma derivWithin_right {σ ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Ici t) t :=
  (hH t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

lemma derivWithin_left {σ ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Icc 0 T) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Iic t) t :=
  (hH t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE_of_mem ht)

lemma clamp_conj (σ ε : ℝ) (w : ℂ) :
    clamp σ ε (starRingEnd ℂ w) = starRingEnd ℂ (clamp σ ε w) := by
  apply Complex.ext <;> simp [clamp]

lemma velocity_conj (σ ε u : ℝ) (w : ℂ) :
    velocity σ ε u (starRingEnd ℂ w) = starRingEnd ℂ (velocity σ ε u w) := by
  unfold velocity
  rw [map_div₀,map_ofNat,← clamp_conj, map_sub,Complex.conj_ofReal]

lemma conjugate_deriv {σ ε T : ℝ} {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => starRingEnd ℂ (H s))
      (velocity σ ε (U t) (starRingEnd ℂ (H t))) (Icc 0 T) t := by
  intro t ht
  have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (hH t ht)
  simpa only [Function.comp_def,Complex.conjCLE_apply,ContinuousLinearEquiv.coe_coe,
    ← velocity_conj] using hh

lemma positive_height {σ ε T : ℝ} (hσ : |σ| = 1) (hε : 0 < ε)
    {U : ℝ → ℝ} {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Icc 0 T) t)
    (h0 : 0 < (H 0).im) : ∀ t ∈ Icc 0 T, 0 < (H t).im := by
  intro t ht
  have hn (s : ℝ) (hs : s ∈ Icc 0 T) : (H s).im ≠ 0 := by
    intro hs0
    have hr : ∀ t ∈ Icc 0 s, HasDerivWithinAt H
        (velocity σ ε (U t) (H t)) (Icc 0 s) t := fun t ht =>
      (hH t ⟨ht.1,ht.2.trans hs.2⟩).mono (Icc_subset_Icc le_rfl hs.2)
    have hc := conjugate_deriv hr
    have hf : H s = starRingEnd ℂ (H s) := by
      apply Complex.ext <;> simp [hs0]
    have he := ODE_solution_unique_of_mem_Icc_left
      (s:=fun _ => univ) (fun t _ => (velocity_lipschitz hσ hε (U t)).lipschitzOnWith)
      (HasDerivWithinAt.continuousOn hr) (fun _ ht => derivWithin_left hr ht)
      (fun _ _ => mem_univ _) (HasDerivWithinAt.continuousOn hc)
      (fun _ ht => derivWithin_left hc ht) (fun _ _ => mem_univ _) hf
    have hh := congrArg Complex.im (he ⟨le_rfl,hs.1⟩)
    simp only [Complex.conj_im] at hh
    linarith
  by_contra hneg
  have hi := intermediate_value_Icc' ht.1
    ((Complex.continuous_im.comp_continuousOn (HasDerivWithinAt.continuousOn hH)).mono (Icc_subset_Icc le_rfl ht.2))
  obtain ⟨s,hs,hs0⟩ := hi (a:=0) ⟨le_of_not_gt hneg,h0.le⟩
  exact hn s ⟨hs.1,hs.2.trans ht.2⟩ hs0

lemma solution_dist_le {σ ε T D δ : ℝ} (hσ : |σ| = 1) (hε : 0 < ε)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) {U V : ℝ → ℝ} {H G : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H (velocity σ ε (U t) (H t)) (Icc 0 T) t)
    (hG : ∀ t ∈ Icc 0 T, HasDerivWithinAt G (velocity σ ε (V t) (G t)) (Icc 0 T) t)
    (h0 : dist (H 0) (G 0) ≤ δ) (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ D)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (H t) (G t) ≤ (δ+D)*Real.exp ((4/ε^2)*T) := by
  let K : ℝ≥0 := ⟨4/ε^2,by positivity⟩
  have hK : (0:ℝ) < K := by change 0 < 4/ε^2; positivity
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      dist (velocity σ ε (V s) (G s)) (velocity σ ε (U s) (G s)) ≤ (K:ℝ)*D := by
    rw [dist_eq_norm]
    calc
      _ ≤ (4/ε^2)*|V s-U s| := norm_velocity_driver_sub_le hσ hε _ _ _
      _ ≤ (K:ℝ)*D := by
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hUV s ⟨hs.1,hs.2.le⟩) hK.le
  have hh := dist_le_of_approx_trajectories_ODE
    (fun t => velocity_lipschitz hσ hε (U t))
    (HasDerivWithinAt.continuousOn hH) (fun _ hs => derivWithin_right hH hs)
    (fun t _ => le_of_eq (dist_self (velocity σ ε (U t) (H t))))
    (HasDerivWithinAt.continuousOn hG) (fun _ hs => derivWithin_right hG hs)
    hb h0 t ht
  have he : gronwallBound δ K (0+(K:ℝ)*D) (t-0) =
      δ*Real.exp ((K:ℝ)*t)+D*(Real.exp ((K:ℝ)*t)-1) := by
    simp only [gronwallBound,zero_add,sub_zero,ite_eq_right (ne_of_gt hK)]
    field_simp
  rw [he] at hh
  have hexp : Real.exp ((K:ℝ)*t) ≤ Real.exp ((K:ℝ)*T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK.le)
  apply hh.trans
  change δ*Real.exp ((K:ℝ)*t)+D*(Real.exp ((K:ℝ)*t)-1) ≤ (δ+D)*Real.exp ((K:ℝ)*T)
  have h1 := mul_le_mul_of_nonneg_left hexp hδ
  have h2 := mul_le_mul_of_nonneg_left hexp hD
  nlinarith

end SLEExactGauge.BoundaryCutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

structure Gauge where
  toFun : ℝ≥0 → ℝ≥0
  continuous : Continuous toFun
  monotone : Monotone toFun
  zero : toFun 0 = 0
  positive : ∀ r, 0 < r → 0 < toFun r

instance : CoeFun Gauge (fun _ => ℝ≥0 → ℝ≥0) := ⟨Gauge.toFun⟩

def Gauge.extended (h : Gauge) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ∞ else (h r.toNNReal : ℝ≥0∞)

def Gauge.hausdorff (h : Gauge) : Measure ℂ :=
  Measure.mkMetric h.extended

def IsExactGauge (κ : ℝ) (h : Gauge) : Prop :=
  ∃ r₀ : ℝ≥0, 0 < r₀ ∧ ∀ r : ℝ≥0, 0 < r → r < r₀ →
    (h r : ℝ) = (r : ℝ) ^ dimension κ *
      (Real.log (Real.log (1 / (r : ℝ)))) ^ (codimension κ / 2)

def IsLargerGauge (κ : ℝ) (g : Gauge) : Prop :=
  ∃ r₀ : ℝ≥0, 0 < r₀ ∧ ∀ r : ℝ≥0, 0 < r → r < r₀ →
    (g r : ℝ) = (r : ℝ) ^ dimension κ * Real.log (Real.log (1 / (r : ℝ)))

def halfPlane : Set ℂ := {z | 0 < z.im}

def localizationSegment (γ : ℝ → ℂ) (s t : ℝ) : Set ℂ := γ '' Icc s t

def localizationWholeTrace (γ : ℝ → ℂ) : Set ℂ := γ '' Ici 0

def rectangle (m : ℕ) : Set ℂ :=
  {z | -(m : ℝ) ≤ z.re ∧ z.re ≤ m ∧ 0 ≤ z.im ∧ z.im ≤ m}

def localizationDomain (γ : ℝ → ℂ) (t : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane \ localizationSegment γ 0 t ∧
    ¬ Bornology.IsBounded (connectedComponentIn (halfPlane \ localizationSegment γ 0 t) z)}

def IsLoewnerTrace (driver : ℝ → ℝ) (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Ici 0) ∧ γ 0 = 0 ∧
  (∀ t, 0 ≤ t → 0 ≤ (γ t).im) ∧
  Tendsto γ atTop (Bornology.cobounded ℂ) ∧
  ∃ g f : ℝ → ℂ → ℂ,
    (∀ z ∈ halfPlane, g 0 z = z) ∧
    (∀ t, 0 ≤ t → AnalyticOnNhd ℂ (g t) (localizationDomain γ t)) ∧
    (∀ t, 0 ≤ t → AnalyticOnNhd ℂ (f t) halfPlane) ∧
    (∀ t, 0 ≤ t → MapsTo (g t) (localizationDomain γ t) halfPlane) ∧
    (∀ t, 0 ≤ t → MapsTo (f t) halfPlane (localizationDomain γ t)) ∧
    (∀ t, 0 ≤ t → ∀ z ∈ localizationDomain γ t, f t (g t z) = z) ∧
    (∀ t, 0 ≤ t → ∀ z ∈ halfPlane, g t (f t z) = z) ∧
    (∀ z ∈ halfPlane,
      ContinuousOn (fun t => g t z) {t | 0 ≤ t ∧ z ∈ localizationDomain γ t}) ∧
    (∀ t, 0 < t → ∀ z ∈ localizationDomain γ t,
      HasDerivAt (fun u => g u z) (2 / (g t z - (driver t : ℂ))) t) ∧
    (∀ t, 0 ≤ t → Tendsto
      (fun y : ℝ => f t ((driver t : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (γ t)))

def IsChordalSLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (P : Measure Ω) (γ : Ω → ℝ → ℂ) : Prop :=
  (∀ t, 0 ≤ t → AEMeasurable (fun ω => γ ω t) P) ∧
  ∃ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧
    ∀ᵐ ω ∂P, IsLoewnerTrace (fun t => Real.sqrt κ * B t.toNNReal ω) (γ ω)

def LocalizationMainEvent (h : Gauge) (γ : ℝ → ℂ) : Prop :=
  (∀ s t : ℝ, 0 < s → s < t →
    0 < h.hausdorff (localizationSegment γ s t) ∧ h.hausdorff (localizationSegment γ s t) < ∞) ∧
  (∀ m : ℕ, 0 < m → h.hausdorff (localizationWholeTrace γ ∩ rectangle m) < ∞)

def LocalizationMainConclusion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : Ω → ℝ → ℂ) (h : Gauge) : Prop :=
  (∀ᵐ ω ∂P, LocalizationMainEvent h (γ ω)) ∧
  (∀ R : ℝ, 0 < R → ∃ C : ℝ≥0,
    (∫⁻ ω, h.hausdorff (localizationWholeTrace (γ ω) ∩ Metric.closedBall 0 R) ∂P) ≤ C)

def LargerGaugeConclusion (g : Gauge) (γ : ℝ → ℂ) : Prop :=
  ∀ s t : ℝ, 0 < s → s < t →
    ¬ SigmaFinite (g.hausdorff.restrict (localizationSegment γ s t)) ∧
      g.hausdorff (localizationSegment γ s t) = ∞

def IsLoewnerTraceUsing (driver : ℝ → ℝ) (γ : ℝ → ℂ)
    (g f : ℝ → ℂ → ℂ) : Prop :=
  ContinuousOn γ (Ici 0) ∧ γ 0 = 0 ∧
  (∀ t, 0 ≤ t → 0 ≤ (γ t).im) ∧
  Tendsto γ atTop (Bornology.cobounded ℂ) ∧
    (∀ z ∈ halfPlane, g 0 z = z) ∧
    (∀ t, 0 ≤ t → AnalyticOnNhd ℂ (g t) (localizationDomain γ t)) ∧
    (∀ t, 0 ≤ t → AnalyticOnNhd ℂ (f t) halfPlane) ∧
    (∀ t, 0 ≤ t → MapsTo (g t) (localizationDomain γ t) halfPlane) ∧
    (∀ t, 0 ≤ t → MapsTo (f t) halfPlane (localizationDomain γ t)) ∧
    (∀ t, 0 ≤ t → ∀ z ∈ localizationDomain γ t, f t (g t z) = z) ∧
    (∀ t, 0 ≤ t → ∀ z ∈ halfPlane, g t (f t z) = z) ∧
    (∀ z ∈ halfPlane,
      ContinuousOn (fun t => g t z) {t | 0 ≤ t ∧ z ∈ localizationDomain γ t}) ∧
    (∀ t, 0 < t → ∀ z ∈ localizationDomain γ t,
      HasDerivAt (fun u => g u z) (2 / (g t z - (driver t : ℂ))) t) ∧
    (∀ t, 0 ≤ t → Tendsto
      (fun y : ℝ => f t ((driver t : ℂ) + (y : ℂ) * Complex.I))
      (𝓝[>] 0) (𝓝 (γ t)))

def loewnerRadius (g : ℝ → ℂ → ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  2 * (g t z).im / ‖deriv (g t) z‖

def loewnerAngleSine (κ : ℝ) (B : ℝ≥0 → ℝ)
    (g : ℝ → ℂ → ℂ) (t : ℝ) (z : ℂ) : ℝ :=
  (g t z).im / ‖g t z - (Real.sqrt κ * B t.toNNReal : ℂ)‖

def firstLiveRadiusStop (γ : ℝ → ℂ) (g : ℝ → ℂ → ℂ)
    (z : ℂ) (u : ℝ) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) ''
    {t : ℝ≥0 | z ∈ localizationDomain γ t ∧
      loewnerRadius g t z = (2 * z.im) * Real.exp (-u)})

def finiteStoppedDensity (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ → ℂ)
    (g : ℝ → ℂ → ℂ) (z : ℂ) (u : ℝ) : ℝ≥0∞ :=
  let τ := firstLiveRadiusStop γ g z u
  if τ = ∞ then 0 else
    ENNReal.ofReal ((loewnerRadius g τ.toReal z) ^ (-codimension κ) *
      (loewnerAngleSine κ B g τ.toReal z) ^ (8 / κ - 1))

lemma halfPlane_open : IsOpen halfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

lemma halfPlane_preconnected : IsPreconnected halfPlane :=
  (convex_halfSpace_im_gt 0).isPreconnected

lemma halfPlane_not_bounded : ¬ Bornology.IsBounded halfPlane := by
  intro hb
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_lt
  have hm : ((R : ℂ) * Complex.I) ∈ halfPlane := by
    simpa [halfPlane] using hR
  have hh := hbound _ hm
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_of_pos hR] at hh
  exact lt_irrefl _ hh

lemma survivingDomain_mono {γ : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) :
    localizationDomain γ t ⊆ localizationDomain γ s := by
  have hsub : halfPlane \ localizationSegment γ 0 t ⊆ halfPlane \ localizationSegment γ 0 s := by
    apply sdiff_subset_sdiff_right
    exact image_mono (Icc_subset_Icc le_rfl hst)
  intro z hz
  exact ⟨hsub hz.1, fun hb => hz.2 (hb.subset (connectedComponentIn_mono z hsub))⟩

lemma survivingDomain_zero {γ : ℝ → ℂ} (hγ : γ 0 = 0) :
    localizationDomain γ 0 = halfPlane := by
  have hset : halfPlane \ localizationSegment γ 0 0 = halfPlane := by
    simp only [localizationSegment, Icc_self, image_singleton, hγ]
    apply sdiff_singleton_eq_self
    simp [halfPlane]
  ext z
  constructor
  · exact fun h => h.1.1
  · intro hz
    refine ⟨by simpa only [hset] using hz, ?_⟩
    rw [hset]
    intro hb
    exact halfPlane_not_bounded (hb.subset
      (halfPlane_preconnected.subset_connectedComponentIn hz subset_rfl))

lemma survivingDomain_open {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0))
    {t : ℝ} (_ht : 0 ≤ t) : IsOpen (localizationDomain γ t) := by
  have hc : IsCompact (localizationSegment γ 0 t) :=
    isCompact_Icc.image_of_continuousOn (hγ.mono (fun _ ha => ha.1))
  have hF : IsOpen (halfPlane \ localizationSegment γ 0 t) := halfPlane_open.sdiff hc.isClosed
  apply isOpen_iff_mem_nhds.2
  intro z hz
  have ho := hF.connectedComponentIn (x := z)
  have hn := ho.mem_nhds (mem_connectedComponentIn hz.1)
  apply Filter.mem_of_superset hn
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
namespace IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma initial (h : IsLoewnerTraceUsing driver γ g f) :
    ∀ z ∈ halfPlane, g 0 z = z := h.2.2.2.2.1

lemma continuous_eval (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (_hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun t => g t z) (Icc 0 T) := by
  rcases h with ⟨hγ, hzero, him, htrans, hinit, hg, hf, hgmap, hfmap, hfg, hgf, hc, hd, htip⟩
  apply (hc z hz.1.1).mono
  intro t ht
  exact ⟨ht.1, survivingDomain_mono ht.2 hz⟩

lemma im_pos (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    0 < (g t z).im := h.2.2.2.2.2.2.2.1 t ht hz

lemma analytic_eval (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    AnalyticAt ℂ (g t) z := h.2.2.2.2.2.1 t ht z hz

lemma deriv_initial (h : IsLoewnerTraceUsing driver γ g f)
    {z : ℂ} (hz : z ∈ halfPlane) : deriv (g 0) z = 1 := by
  have heq : g 0 =ᶠ[𝓝 z] id := by
    filter_upwards [halfPlane_open.mem_nhds hz] with w hw
    exact h.initial w hw
  rw [heq.deriv_eq]
  exact deriv_id z

lemma hasDerivAt_eval (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    HasDerivAt (fun u => g u z) (2 / (g t z - (driver t : ℂ))) t := by
  rcases h with ⟨hγ, hzero, him, htrans, hinit, hg, hf, hgmap, hfmap, hfg, hgf, hc, hd, htip⟩
  exact hd t ht z hz

lemma deriv_ne_zero (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    deriv (g t) z ≠ 0 := by
  rcases h with ⟨hγ, hzero, him, htrans, hinit, hg, hf, hgmap, hfmap, hfg, hgf, hc, hd, htip⟩
  have hgd := (hg t ht z hz).differentiableAt.hasDerivAt
  have hfd := (hf t ht _ (hgmap t ht hz)).differentiableAt.hasDerivAt
  have heq : (fun w => f t (g t w)) =ᶠ[𝓝 z] id := by
    filter_upwards [(survivingDomain_open hγ ht).mem_nhds hz] with w hw
    exact hfg t ht w hw
  have hh := (hfd.comp z hgd).congr_of_eventuallyEq heq.symm
  have he := hh.unique (hasDerivAt_id z)
  intro hn
  simp [hn] at he

lemma radius_pos (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    0 < loewnerRadius g t z := by
  unfold loewnerRadius
  exact div_pos (mul_pos (by norm_num) (h.im_pos ht hz))
    (norm_pos_iff.2 (h.deriv_ne_zero ht hz))

lemma radius_initial (h : IsLoewnerTraceUsing driver γ g f)
    {z : ℂ} (hz : z ∈ halfPlane) : loewnerRadius g 0 z = 2 * z.im := by
  simp [loewnerRadius, h.initial z hz, h.deriv_initial hz]

lemma centered_ne_zero (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    g t z - (driver t : ℂ) ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  have hp := h.im_pos ht hz
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact hp.ne' hi

lemma hasDerivAt_height (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    HasDerivAt (fun s => (g s z).im)
      (-2 * (g t z).im / Complex.normSq (g t z - (driver t : ℂ))) t := by
  have hh := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (h.hasDerivAt_eval ht hz)
  simpa [Complex.div_im, Function.comp_def, neg_div] using hh

lemma height_antitone (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    AntitoneOn (fun t => (g t z).im) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (Complex.continuous_im.comp_continuousOn (h.continuous_eval hT hz))
    (f' := fun t => -2 * (g t z).im / Complex.normSq (g t z - (driver t : ℂ)))
  · intro t ht
    rw [interior_Icc] at ht
    exact (h.hasDerivAt_height ht.1 (survivingDomain_mono ht.2.le hz)).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (h.im_pos ht.1.le (survivingDomain_mono ht.2.le hz)).le)
      (Complex.normSq_nonneg _)

lemma height_le_initial (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    (g t z).im ≤ z.im := by
  have hh := h.height_antitone ht hz ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simpa only [h.initial z hz.1.1] using hh

lemma continuous_velocity (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun t => 2 / (g t z - (driver t : ℂ))) (Icc 0 T) := by
  apply continuousOn_const.div
    ((h.continuous_eval hT hz).sub (Complex.continuous_ofReal.comp_continuousOn hU))
  intro t ht
  exact h.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hz)

lemma integral_velocity (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    (∫ t in a..b, 2 / (g t z - (driver t : ℂ))) = g b z - g a z := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha.1 hb.2
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    ((h.continuous_eval hT hz).mono hsub)
  · intro t ht
    exact h.hasDerivAt_eval (lt_of_le_of_lt ha.1 ht.1)
      (survivingDomain_mono (ht.2.le.trans hb.2) hz)
  · apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using (h.continuous_velocity hT hU hz).mono hsub

lemma norm_velocity_le (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ localizationDomain γ T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖2 / (g t z - (driver t : ℂ))‖ ≤ 2 / (g T z).im := by
  have hY := h.im_pos hT hz
  have hm : (g T z).im ≤ (g t z).im :=
    h.height_antitone hT hz ht ⟨hT, le_rfl⟩ ht.2
  have hn : (g t z).im ≤ ‖g t z - (driver t : ℂ)‖ := by
    have hh := Complex.im_le_norm (g t z - (driver t : ℂ))
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hh
  rw [norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hY (hm.trans hn)

lemma norm_time_sub_le (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    ‖g b z - g a z‖ ≤ (2 / (g T z).im) * |b - a| := by
  wlog hab : a ≤ b generalizing a b
  · have hh := this hb ha (le_of_not_ge hab)
    simpa only [norm_sub_rev, abs_sub_comm] using hh
  rw [← h.integral_velocity hT hU hz ha hb hab]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun t ht =>
    h.norm_velocity_le hT hz ⟨ha.1.trans (uIoc_of_le hab ▸ ht).1.le,
      (uIoc_of_le hab ▸ ht).2.trans hb.2⟩

end IsLoewnerTraceUsing

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma firstLiveRadiusStop_zero {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {z : ℂ} (hz : z ∈ halfPlane) :
    firstLiveRadiusStop γ g z 0 = 0 := by
  apply le_antisymm ?_ bot_le
  apply sInf_le
  refine ⟨0, ⟨?_, ?_⟩, rfl⟩
  · simpa only [NNReal.coe_zero, survivingDomain_zero h.2.1] using hz
  · simpa only [NNReal.coe_zero, neg_zero, Real.exp_zero, mul_one] using h.radius_initial hz

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

def differenceCoefficient (driver : ℝ → ℝ) (g : ℝ → ℂ → ℂ) (w z : ℂ) (t : ℝ) : ℂ :=
  -2 / ((g t w - (driver t : ℂ)) * (g t z - (driver t : ℂ)))

lemma continuous_differenceCoefficient (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {w z : ℂ} (hw : w ∈ localizationDomain γ T) (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (differenceCoefficient driver g w z) (Icc 0 T) := by
  apply continuousOn_const.div
    (((h.continuous_eval hT hw).sub (Complex.continuous_ofReal.comp_continuousOn hU)).mul
      ((h.continuous_eval hT hz).sub (Complex.continuous_ofReal.comp_continuousOn hU)))
  intro t ht
  exact mul_ne_zero (h.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hw))
    (h.centered_ne_zero ht.1 (survivingDomain_mono ht.2 hz))

lemma difference_eq_exp_integral (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {w z : ℂ} (hw : w ∈ localizationDomain γ T) (hz : z ∈ localizationDomain γ T) :
    g T w - g T z = (w-z) * Complex.exp
      (∫ s in (0 : ℝ)..T, differenceCoefficient driver g w z s) := by
  let a := differenceCoefficient driver g w z
  let A : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, a s
  have ha : ContinuousOn a (Icc 0 T) := h.continuous_differenceCoefficient hT hU hw hz
  have hi : IntervalIntegrable a volume 0 T := ha.intervalIntegrable_of_Icc hT
  have hAc : ContinuousOn A (Icc 0 T) := by
    simpa only [uIcc_of_le hT, A] using
      intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
  have hAd {t : ℝ} (ht : t ∈ Ioo 0 T) : HasDerivAt A (a t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
      (hi.mono_set (by rw [uIcc_of_le ht.1.le, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2.le))
    · have hh := ha.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc t
      rwa [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2)] at hh
    · exact ha.continuousAt (Icc_mem_nhds ht.1 ht.2)
  let R : ℝ → ℂ := fun t => (g t w - g t z) * Complex.exp (-A t)
  have hRc : ContinuousOn R (Icc 0 T) := by
    exact ((h.continuous_eval hT hw).sub (h.continuous_eval hT hz)).mul
      (Complex.continuous_exp.comp_continuousOn hAc.neg)
  have hRd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt R 0 t := by
    have hd := ((h.hasDerivAt_eval ht.1 (survivingDomain_mono ht.2.le hw)).sub
      (h.hasDerivAt_eval ht.1 (survivingDomain_mono ht.2.le hz))).mul (hAd ht).neg.cexp
    apply hd.congr_deriv
    have hw' := h.centered_ne_zero ht.1.le (survivingDomain_mono ht.2.le hw)
    have hz' := h.centered_ne_zero ht.1.le (survivingDomain_mono ht.2.le hz)
    dsimp [a, differenceCoefficient]
    field_simp
    ring
  have hr := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hRc hRd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume 0 T)
  have hR : R T = w-z := by
    apply sub_eq_zero.1
    simpa only [intervalIntegral.integral_zero, R, A, intervalIntegral.integral_same,
      neg_zero, Complex.exp_zero, mul_one, h.initial w hw.1.1, h.initial z hz.1.1,
      ] using hr.symm
  have hexp := Complex.exp_ne_zero (-A T)
  dsimp [R] at hR
  calc
    g T w - g T z = (g T w - g T z) * (Complex.exp (-A T) * Complex.exp (A T)) := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = (w-z) * Complex.exp (A T) := by rw [← mul_assoc, hR]

lemma continuousAt_integral_differenceCoefficient (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousAt (fun w => ∫ s in (0 : ℝ)..T, differenceCoefficient driver g w z s) z := by
  let ε := (g T z).im / 2
  have hε : 0 < ε := half_pos (h.im_pos hT hz)
  have hev : ∀ᶠ w in 𝓝 z, w ∈ localizationDomain γ T ∧ ε ≤ (g T w).im := by
    have hc := Complex.continuous_im.continuousAt.comp (h.analytic_eval hT hz).continuousAt
    have hlt : ε < (g T z).im := by dsimp [ε]; linarith [h.im_pos hT hz]
    filter_upwards [(survivingDomain_open h.1 hT).mem_nhds hz,
      hc.eventually (Ioi_mem_nhds hlt)] with w hw hh
    exact ⟨hw, hh.le⟩
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 2 / ε^2)
  · filter_upwards [hev] with w hw
    have hc := h.continuous_differenceCoefficient hT hU hw.1 hz
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    exact hc.mono (by rw [uIoc_of_le hT]; exact Ioc_subset_Icc_self)
  · filter_upwards [hev] with w hw
    apply ae_of_all
    intro t ht
    rw [uIoc_of_le hT] at ht
    have hwheight : ε ≤ (g t w).im :=
      hw.2.trans (h.height_antitone hT hw.1 ⟨ht.1.le, ht.2⟩ ⟨hT, le_rfl⟩ ht.2)
    have hzheight : ε ≤ (g t z).im := by
      have hhalf : ε ≤ (g T z).im := by dsimp [ε]; linarith [h.im_pos hT hz]
      exact hhalf.trans (h.height_antitone hT hz ⟨ht.1.le, ht.2⟩ ⟨hT, le_rfl⟩ ht.2)
    have hwn : ε ≤ ‖g t w - (driver t : ℂ)‖ := hwheight.trans (by
      simpa using Complex.im_le_norm (g t w - (driver t : ℂ)))
    have hzn : ε ≤ ‖g t z - (driver t : ℂ)‖ := hzheight.trans (by
      simpa using Complex.im_le_norm (g t z - (driver t : ℂ)))
    simp only [differenceCoefficient, norm_div, norm_neg, Complex.norm_ofNat, norm_mul]
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hε)
    simpa only [pow_two] using mul_le_mul hwn hzn hε.le (norm_nonneg _)
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro t ht
    rw [uIoc_of_le hT] at ht
    have hzt := survivingDomain_mono ht.2 hz
    exact continuousAt_const.div
      (((h.analytic_eval ht.1.le hzt).continuousAt.sub continuousAt_const).mul continuousAt_const)
      (mul_ne_zero (h.centered_ne_zero ht.1.le hzt) (h.centered_ne_zero ht.1.le hzt))

lemma spatial_deriv_eq_exp_integral (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    deriv (g T) z = Complex.exp (∫ s in (0 : ℝ)..T,
      -2 / (g s z - (driver s : ℂ))^2) := by
  have hd : HasDerivAt (g T) (Complex.exp (∫ s in (0 : ℝ)..T,
      differenceCoefficient driver g z z s)) z := by
    apply hasDerivAt_iff_tendsto_slope.2
    have hc := Complex.continuous_exp.continuousAt.comp
      (h.continuousAt_integral_differenceCoefficient hT hU hz)
    apply (hc.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((survivingDomain_open h.1 hT).mem_nhds hz)]
      with w hwne hw
    have hwz : w ≠ z := hwne
    dsimp only [slope, vsub_eq_sub, Function.comp_def]
    rw [h.difference_eq_exp_integral hT hU hw hz]
    simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hwz), one_mul]
  have he : (fun s => differenceCoefficient driver g z z s) =
      (fun s => -2 / (g s z - (driver s : ℂ))^2) := by
    funext s
    simp only [differenceCoefficient, pow_two]
  simpa only [he] using hd.deriv

lemma log_deriv_norm_eq (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    Real.log ‖deriv (g T) z‖ =
      (∫ s in (0 : ℝ)..T, -2 / (g s z - (driver s : ℂ))^2).re := by
  rw [h.spatial_deriv_eq_exp_integral hT hU hz, Complex.norm_exp, Real.log_exp]

lemma continuous_spatialCoefficient (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun s => -2 / (g s z - (driver s : ℂ))^2) (Icc 0 T) := by
  have hc := h.continuous_differenceCoefficient hT hU hz hz
  unfold differenceCoefficient at hc
  simpa only [pow_two] using hc

lemma continuous_log_deriv_norm (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun t => Real.log ‖deriv (g t) z‖) (Icc 0 T) := by
  have hi : IntervalIntegrable (fun s => -2 / (g s z - (driver s : ℂ))^2) volume 0 T :=
    (h.continuous_spatialCoefficient hT hU hz).intervalIntegrable_of_Icc hT
  have hc := Complex.continuous_re.comp_continuousOn
    (intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc)
  rw [uIcc_of_le hT] at hc
  apply hc.congr
  intro t ht
  exact h.log_deriv_norm_eq ht.1
    (hU.mono (Icc_subset_Icc le_rfl ht.2)) (survivingDomain_mono ht.2 hz)

lemma hasDerivAt_log_deriv_norm (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Real.log ‖deriv (g s) z‖)
      (-2 / (g t z - (driver t : ℂ))^2).re t := by
  have hc := h.continuous_spatialCoefficient hT hU hz
  have hi : IntervalIntegrable (fun s => -2 / (g s z - (driver s : ℂ))^2) volume 0 t :=
    (hc.intervalIntegrable_of_Icc hT).mono_set (by
      rw [uIcc_of_le ht.1.le, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2.le)
  have hm := hc.stronglyMeasurableAtFilter_nhdsWithin (μ := volume) measurableSet_Icc t
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2)] at hm
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (intervalIntegral.integral_hasDerivAt_right hi hm
      (hc.continuousAt (Icc_mem_nhds ht.1 ht.2)))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact h.log_deriv_norm_eq hs.1 (hU.mono (Icc_subset_Icc le_rfl hs.2))
    (survivingDomain_mono hs.2 hz)

lemma real_spatialCoefficient (w : ℂ) :
    (-2 / w^2).re = -2 * (w.re^2-w.im^2) / (Complex.normSq w)^2 := by
  simp only [Complex.div_re, Complex.neg_re, Complex.re_ofNat, Complex.neg_im,
    Complex.im_ofNat, neg_zero, zero_mul, map_pow]
  simp only [pow_two, Complex.mul_re]
  ring

lemma log_radius_eq (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    Real.log (loewnerRadius g t z) = Real.log 2 + Real.log (g t z).im -
      Real.log ‖deriv (g t) z‖ := by
  rw [loewnerRadius, Real.log_div (mul_ne_zero (by norm_num) (h.im_pos ht hz).ne')
    (norm_ne_zero_iff.2 (h.deriv_ne_zero ht hz)),
    Real.log_mul (by norm_num) (h.im_pos ht hz).ne']

lemma continuous_log_radius (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun t => Real.log (loewnerRadius g t z)) (Icc 0 T) := by
  have hc := ((Complex.continuous_im.comp_continuousOn (h.continuous_eval hT hz)).log
    (fun t ht => (h.im_pos ht.1 (survivingDomain_mono ht.2 hz)).ne')).const_add (Real.log 2)
  apply (hc.sub (h.continuous_log_deriv_norm hT hU hz)).congr
  intro t ht
  exact h.log_radius_eq ht.1 (survivingDomain_mono ht.2 hz)

lemma hasDerivAt_log_radius (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Real.log (loewnerRadius g s z))
      (-4 * (g t z).im^2 / (Complex.normSq (g t z - (driver t : ℂ)))^2) t := by
  have hzt := survivingDomain_mono ht.2.le hz
  have hY := h.im_pos ht.1.le hzt
  have hd := (((h.hasDerivAt_height ht.1 hzt).log hY.ne').const_add (Real.log 2)).sub
    (h.hasDerivAt_log_deriv_norm hT hU hz ht)
  have he : HasDerivAt (fun s => Real.log (loewnerRadius g s z))
      ((-2 * (g t z).im / Complex.normSq (g t z - (driver t : ℂ))) / (g t z).im -
        (-2 / (g t z - (driver t : ℂ))^2).re) t := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact h.log_radius_eq hs.1 (survivingDomain_mono hs.2 hz)
  apply he.congr_deriv
  rw [real_spatialCoefficient]
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  field_simp
  ring

lemma continuous_radius (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    ContinuousOn (fun t => loewnerRadius g t z) (Icc 0 T) := by
  apply (Real.continuous_exp.comp_continuousOn (h.continuous_log_radius hT hU hz)).congr
  intro t ht
  exact (Real.exp_log (h.radius_pos ht.1 (survivingDomain_mono ht.2 hz))).symm

lemma log_radius_strictAnti (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    StrictAntiOn (fun t => Real.log (loewnerRadius g t z)) (Icc 0 T) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 T)
    (h.continuous_log_radius hT hU hz)
    (f' := fun t => -4 * (g t z).im^2 / (Complex.normSq (g t z - (driver t : ℂ)))^2)
  · intro t ht
    rw [interior_Icc] at ht
    exact (h.hasDerivAt_log_radius hT hU hz ht).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have hzt := survivingDomain_mono ht.2.le hz
    have hy := h.im_pos ht.1.le hzt
    have hq := Complex.normSq_pos.2 (h.centered_ne_zero ht.1.le hzt)
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hy))
      (sq_pos_of_pos hq)

lemma radius_strictAnti (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) :
    StrictAntiOn (fun t => loewnerRadius g t z) (Icc 0 T) := by
  intro s hs t ht hst
  exact (Real.log_lt_log_iff (h.radius_pos ht.1 (survivingDomain_mono ht.2 hz))
    (h.radius_pos hs.1 (survivingDomain_mono hs.2 hz))).1
      (h.log_radius_strictAnti hT hU hz hs ht hst)

lemma live_radius_injective (h : IsLoewnerTraceUsing driver γ g f)
    (hU : ContinuousOn driver (Ici 0)) {z : ℂ} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hzs : z ∈ localizationDomain γ s)
    (hzt : z ∈ localizationDomain γ t) (he : loewnerRadius g s z = loewnerRadius g t z) :
    s = t := by
  rcases le_total s t with hst | hts
  · exact (h.radius_strictAnti ht (hU.mono Icc_subset_Ici_self) hzt).injOn
      ⟨hs, hst⟩ ⟨ht, le_rfl⟩ he
  · exact (h.radius_strictAnti hs (hU.mono Icc_subset_Ici_self) hzs).injOn
      ⟨hs, le_rfl⟩ ⟨ht, hts⟩ he

lemma firstLiveRadiusStop_eq (h : IsLoewnerTraceUsing driver γ g f)
    (hU : ContinuousOn driver (Ici 0)) {z : ℂ} {u : ℝ} {t : ℝ≥0}
    (hzt : z ∈ localizationDomain γ t)
    (he : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) :
    firstLiveRadiusStop γ g z u = (t : ℝ≥0∞) := by
  have heq : {s : ℝ≥0 | z ∈ localizationDomain γ s ∧
      loewnerRadius g s z = (2*z.im)*Real.exp (-u)} = {t} := by
    ext s
    constructor
    · intro hs
      apply mem_singleton_iff.2
      apply NNReal.coe_injective
      exact h.live_radius_injective hU s.coe_nonneg t.coe_nonneg hs.1 hzt (hs.2.trans he.symm)
    · rintro rfl
      exact ⟨hzt, he⟩
  simp only [firstLiveRadiusStop, heq, image_singleton, sInf_singleton]

end SLEExactGauge.IsLoewnerTraceUsing

end

end

end OAI
