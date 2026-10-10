import OAI.Probability.FirstPassage.CrossingTilt

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem norm_direction_pos (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (b : ℝ) :
    0 < μ (direction b) := by
  have hn : direction b ≠ 0 := by
    intro hh
    have := congrArg xCoord hh
    norm_num [direction] at this
  exact lt_of_le_of_ne (hμ.nonneg _) (Ne.symm ((hμ.zero_iff _).not.mpr hn))

theorem exponential_crossing_cubic_tendsto {ι : Type*} {l : Filter ι}
    (h : ExponentialEnvironment P τ) (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (ht : IsTimeConstant P τ μ) (b K : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (s : ι → ℝ) (n : ι → ℤ) (hs : Tendsto s l atTop)
    (hn3 : ∀ᶠ i in l, (s i)^3 ≤ n i) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b (μ (direction b)) K (s i) (n i) 0}) l (𝓝 0) := by
  let m := μ (direction b)
  let a := extremeSlope μ b true
  let lam := (K+16*|a|+2)/m
  have hm : 0 < m := norm_direction_pos μ hμ b
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
  have hrare := exponential_rareFast_tendsto h μ hμ ht b 1 8 1 hb (by norm_num) (by norm_num)
    (by norm_num) true s n hs hratio
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le measureReal_nonneg)
  · intro κ hκ
    have hC : 0 < Real.exp (288*lam^2) := Real.exp_pos _
    filter_upwards [hs.eventually (eventually_ge_atTop (max 1 (2*lam))),hn3,
      (tendsto_order.1 hrare).2 (κ^2/Real.exp (288*lam^2)) (by positivity)] with i hsi hni hpi
    have hs1 : 1 ≤ s i := (le_max_left _ _).trans hsi
    have hslam : 2*lam ≤ s i := (le_max_right _ _).trans hsi
    have hquad : (s i)^2 ≤ (s i)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sq_nonneg (s i))]
    have hn1 : (1 : ℝ) ≤ n i := by nlinarith
    have hn1' : 1 ≤ n i := by exact_mod_cast hn1
    have hsmall : lam*s i/(n i : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < n i)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hslam (by linarith : 0 ≤ s i)]
    have hh := exponential_crossing_tilt_bound h b m a K lam (s i) (n i) hK hlam.le hs1 hn1' hni hsmall hgain
    have hh' := (lt_div_iff₀ hC).mp hpi
    nlinarith [measureReal_nonneg (μ := P) (s := {ω | (fun e => τ e ω) ∈ crossingEvent b m K (s i) (n i) 0})]

noncomputable def sourceCrossingK (μ : Plane → ℝ) (b : ℝ) : ℝ :=
  100*(1+|extremeSlope μ b false|+|extremeSlope μ b true|)

theorem exponential_source_tilt (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b : ℝ) (hb : |b| ≤ 1) :
    Tendsto (fun k : ℕ => P.real {ω | (fun e => τ e ω) ∈
      crossingEvent b (μ (direction b)) (sourceCrossingK μ b) ((2 : ℝ)^k) ((2 : ℤ)^(3*k)) 0})
      atTop (𝓝 0) := by
  apply exponential_crossing_cubic_tendsto h μ hμ ht b (sourceCrossingK μ b) hb
    (by unfold sourceCrossingK; positivity) (fun k : ℕ => (2 : ℝ)^k) (fun k => (2 : ℤ)^(3*k))
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ)<2))
  apply Eventually.of_forall
  intro k
  norm_num only [Int.cast_pow,Int.cast_ofNat]
  rw [← pow_mul,Nat.mul_comm k 3]

end PlanarFPP

end OAI
