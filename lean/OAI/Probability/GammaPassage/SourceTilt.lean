import OAI.Probability.GammaPassage.CrossingTilt
import OAI.Probability.GammaPassage.RareFast
import OAI.Probability.GammaPassage.CoordinateTails

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.IntervalTravelBridge Set Filter MeasureTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

/-- A stronger form of gr:tilt: any integer n >= s^3 works. In particular,
no dyadic-grid property is used in the measure-change argument. -/
theorem gamma_crossing_cubic_tendsto {ι : Type*} {l : Filter ι}
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate) (b K : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (s : ι → ℝ) (n : ι → ℤ) (hs : Tendsto s l atTop)
    (hn3 : ∀ᶠ i in l, (s i)^3 ≤ n i) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) K (s i) (n i) 0}) l (𝓝 0) := by
  let m := (gammaMeanNorm h hshape hrate) (direction b)
  let a := extremeSlope (gammaMeanNorm h hshape hrate) b true
  let lam := (K+16*|a|+2)/m
  have hm : 0 < m := norm_direction_pos (gammaMeanNorm h hshape hrate) (gammaMeanNorm_laws h hshape hrate) b
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hgain : K+16*|a|+1 < lam*m := by
    dsimp [lam]
    rw [div_mul_cancel₀ _ (ne_of_gt hm)]
    linarith
  have hratio : Tendsto (fun i => (n i : ℝ)/s i) l atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 B)),hn3] with i hsi hni
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hsB : B ≤ s i := (le_max_right _ _).trans hsi
    apply (le_div_iff₀ (by linarith : 0 < s i)).mpr
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    nlinarith [mul_le_mul_of_nonneg_right hsB (by linarith : 0 ≤ s i)]
  have hrare := gamma_rareFast_tendsto h hshape hrate b 1 8 1 hb (by norm_num) (by norm_num)
    (by norm_num) true s n hs hratio
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le measureReal_nonneg)
  · intro κ hκ
    have hC : 0 < Real.exp (288*shape*lam^2) := Real.exp_pos _
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 (2*lam))),hn3,
      (tendsto_order.1 hrare).2 (κ^2/Real.exp (288*shape*lam^2)) (by positivity)] with i hsi hni hpi
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hslam : 2*lam ≤ s i := (le_max_right _ _).trans hsi
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    have hn1 : (1 : ℝ) ≤ n i := by nlinarith
    have hn1' : 1 ≤ n i := by exact_mod_cast hn1
    have hsmall : lam*s i/(n i : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < n i)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hslam (by linarith : 0 ≤ s i)]
    have hh := gamma_crossing_tilt_bound h hshape hrate b m a K lam (s i) (n i) hK hlam.le hs1 hn1' hni hsmall hgain
    have hh' := (lt_div_iff₀ hC).mp hpi
    nlinarith [measureReal_nonneg (μ := P) (s := {ω | (fun e => τ e ω) ∈ crossingEvent b m K (s i) (n i) 0})]

noncomputable def sourceCrossingK (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) : ℝ :=
  100*(1+|extremeSlope μ b false|+|extremeSlope μ b true|+|coordinateAllowance shape rate|)

theorem sourceCrossingK_ge_hundred (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) :
    100 ≤ sourceCrossingK shape rate μ b := by
  unfold sourceCrossingK
  nlinarith [abs_nonneg (extremeSlope μ b false), abs_nonneg (extremeSlope μ b true),
    abs_nonneg (coordinateAllowance shape rate)]

theorem sourceCrossingK_ge_coordinateAllowance (shape rate : ℝ) (μ : Plane → ℝ) (b : ℝ) :
    coordinateAllowance shape rate ≤ sourceCrossingK shape rate μ b := by
  unfold sourceCrossingK
  nlinarith [abs_nonneg (extremeSlope μ b false), abs_nonneg (extremeSlope μ b true),
    abs_nonneg (coordinateAllowance shape rate), le_abs_self (coordinateAllowance shape rate)]

/-- Dyadic tilt limit with a Gamma geometric and coordinate allowance. -/
theorem gamma_source_tilt (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b : ℝ) (hb : |b| ≤ 1) :
    Tendsto (fun k : ℕ => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b) ((2 : ℝ)^k) ((2 : ℤ)^(3*k)) 0})
      atTop (𝓝 0) := by
  apply gamma_crossing_cubic_tendsto h hshape hrate b (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b) hb
    (by unfold sourceCrossingK; positivity) (fun k : ℕ => (2 : ℝ)^k) (fun k => (2 : ℤ)^(3*k))
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2))
  apply Eventually.of_forall
  intro k
  norm_num only [Int.cast_pow,Int.cast_ofNat]
  rw [← pow_mul,Nat.mul_comm k 3]

end GammaFPP.CrossingBridge

end OAI
