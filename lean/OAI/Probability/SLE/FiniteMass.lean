import Mathlib
import OAI.Probability.SLE.MeasureSupport
import OAI.Probability.SLE.SpatialMeans

namespace OAI

/-! Finite Mass for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}
lemma continuous_radius_density_crossing
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hz : z ∈ upperHalfPlane)
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (w U : ℝ≥0) (hwU : w ≤ U) (δ : ℝ) :
    finiteCenteredLaw P κ B γ G z U
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc 0 w,
        limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω < δ} ≤
      ENNReal.ofReal (δ / initialGreen κ z) := by
  apply continuous_crossing_from_monotone _ _ _ 0 w U bot_le hwU
  · intro ω hω
    exact (terminalRadiusKernel_continuousOn a hε hBc _ _ U ω hω).mono
      (Icc_subset_Icc le_rfl hwU)
  · intro ω hω s hs
    exact terminalRadiusKernel_pos a hε _ _ U s (hs.2.trans hwU) ω hω
  · intro s hs hvs hsU N
    apply (finite_radius_density_crossing hB hBm hBc hB0 hκ hκ8 γ G F hw hz
      a hε hεlim 0 U s hs hvs hsU δ N).trans
    simpa only [mul_one] using mul_le_mul'
      (le_refl (ENNReal.ofReal (δ / initialGreen κ z)))
      (show P {ω | localizedRadiusStop (a 0) ω < ⊤} ≤ 1 from prob_le_one)

noncomputable def initialAngleWindowConstant (κ : ℝ) (z : ℂ) : ℝ :=
  Real.exp (codimension κ * (1 - Real.log 2 - Real.log z.im)) / initialGreen κ z

lemma initial_inverse_angle_window_bound
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hz : z ∈ upperHalfPlane)
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (w U : ℝ≥0) (hw : w ≤ 1) (hwU : w ≤ U) (L : ℝ) (hL : 0 < L) :
    finiteCenteredLaw P κ B γ G z U
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc 0 w, L < radiusInverseAngle a s ω} ≤
      ENNReal.ofReal (initialAngleWindowConstant κ z / L) := by
  have hs : {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc 0 w, L < radiusInverseAngle a s ω} ⊆
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc 0 w,
        limitRadiusKernel (a s) (codimension κ) (greenExponent κ) s ω <
          Real.exp (codimension κ * ((w : ℝ) - Real.log 2 - Real.log z.im)) / L} := by
    rintro ω ⟨hω, s, hs, hV⟩
    exact ⟨hω, s, hs, radiusInverseAngle_large_imp_crossing a hε hκ8 s w U hs.2 hwU L hL ω hω hV⟩
  apply (measure_mono hs).trans
  apply (continuous_radius_density_crossing hB hBm hBc hB0 hκ hκ8 γ G F ‹∀ᵐ ω ∂P, _› hz
    a hε hεlim w U hwU _).trans
  apply ENNReal.ofReal_le_ofReal
  unfold initialAngleWindowConstant
  rw [div_right_comm _ L]
  apply div_le_div_of_nonneg_right ?_ hL.le
  apply div_le_div_of_nonneg_right ?_ (initialGreen_pos κ z hz).le
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (codimension_pos κ hκ8).le
  exact sub_le_sub_right (sub_le_sub_right (show (w : ℝ) ≤ 1 from hw) _) _

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma sum_exp_decay (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : 0 ≤ C) :
    (∑' n : ℕ, ENNReal.ofReal (C * Real.exp (-η * n))) =
      ENNReal.ofReal (C / (1 - Real.exp (-η))) := by
  have hr : Real.exp (-η) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hη)
  have hn : ∀ n : ℕ, Real.exp (-η * n) = Real.exp (-η) ^ n := fun n => by
    rw [mul_comm, Real.exp_nat_mul]
  simp_rw [hn]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hC (pow_nonneg (Real.exp_pos _).le _))
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left C),
    tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr, div_eq_mul_inv]

lemma exponential_envelope_bound
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (V : ℝ≥0 → Ω → ℝ) (E : Set Ω) (U : ℝ≥0)
    (η M C : ℝ) (hη : 0 < η) (hM : 0 < M) (hC : 0 ≤ C)
    (hwindow : ∀ n : ℕ, Q {ω | ω ∈ E ∧ ∃ s ∈ Icc (n : ℝ≥0) (min (n + 1) U),
      M * Real.exp (η * n) < V s ω} ≤ ENNReal.ofReal (C / (M * Real.exp (η * n)))) :
    Q {ω | ω ∈ E ∧ ∃ s ∈ Icc 0 U, M * Real.exp (η * s) < V s ω} ≤
      ENNReal.ofReal (C / M / (1 - Real.exp (-η))) := by
  let W (n : ℕ) : Set Ω := {ω | ω ∈ E ∧ ∃ s ∈ Icc (n : ℝ≥0) (min (n + 1) U),
      M * Real.exp (η * n) < V s ω}
  have hsub : {ω | ω ∈ E ∧ ∃ s ∈ Icc 0 U, M * Real.exp (η * s) < V s ω} ⊆ ⋃ n, W n := by
    rintro ω ⟨hω, s, hs, hv⟩
    let n : ℕ := ⌊(s : ℝ)⌋₊
    have hn : (n : ℝ) ≤ s := Nat.floor_le s.coe_nonneg
    have hu : (s : ℝ) ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one (s : ℝ)).le
    apply mem_iUnion.mpr
    refine ⟨n, hω, s, ?_, ?_⟩
    · exact ⟨by exact_mod_cast hn, le_min (by exact_mod_cast hu) hs.2⟩
    · apply lt_of_le_of_lt _ hv
      apply mul_le_mul_of_nonneg_left _ hM.le
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn hη.le)
  calc
    _ ≤ Q (⋃ n, W n) := measure_mono hsub
    _ ≤ ∑' n, Q (W n) := measure_iUnion_le W
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C / (M * Real.exp (η * n))) := ENNReal.tsum_le_tsum hwindow
    _ = _ := by
      have he (n : ℕ) : C / (M * Real.exp (η * n)) = (C / M) * Real.exp (-η * n) := by
        rw [neg_mul, Real.exp_neg]
        ring
      simp_rw [he]
      exact sum_exp_decay η hη (C / M) (div_nonneg hC hM.le)

lemma integral_exp_neg_half_le_two (u : ℝ) :
    (∫ s in (0 : ℝ)..u, Real.exp (-s / 2)) ≤ 2 := by
  have hd (s : ℝ) : HasDerivAt (fun s => -2 * Real.exp (-s / 2)) (Real.exp (-s / 2)) s := by
    convert (((Real.hasDerivAt_exp (-s / 2)).comp s ((hasDerivAt_id s).neg.div_const 2)).const_mul (-2)) using 1
    all_goals first | rfl | ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).intervalIntegrable 0 u)]
  norm_num
  nlinarith [Real.exp_pos (-u / 2)]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def angleEnvelopeConstant (κ : ℝ) (z : ℂ) : ℝ :=
  max (initialAngleWindowConstant κ z) (uniformInverseAngleConstant κ 1 * Real.exp (codimension κ))

lemma angleEnvelopeConstant_pos (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    0 < angleEnvelopeConstant κ z :=
  (div_pos (Real.exp_pos _) (initialGreen_pos κ z hz)).trans_le (le_max_left _ _)

lemma finite_inverse_angle_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    {z : ℂ} (hz : z ∈ upperHalfPlane) {ε : ℕ → ℝ}
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (U : ℝ≥0) (M : ℝ) (hM : 0 < M) :
    finiteCenteredLaw P κ B γ G z U
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc 0 U,
        M * Real.exp (greenExponent κ / 8 * s) < radiusInverseAngle a s ω} ≤
      ENNReal.ofReal (angleEnvelopeConstant κ z / M / (1 - Real.exp (-greenExponent κ / 8))) := by
  have hrate : 0 < greenExponent κ / 8 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
  have hC := angleEnvelopeConstant_pos κ z hz
  have he : -(greenExponent κ / 8) = -greenExponent κ / 8 := by ring
  rw [← he]
  apply exponential_envelope_bound (finiteCenteredLaw P κ B γ G z U) (radiusInverseAngle a)
    {ω | localizedRadiusStop (a U) ω < ⊤} U (greenExponent κ / 8) M
    (angleEnvelopeConstant κ z) hrate hM hC.le
  intro n
  let L := M * Real.exp (greenExponent κ / 8 * n)
  have hL : 0 < L := mul_pos hM (Real.exp_pos _)
  change finiteCenteredLaw P κ B γ G z U
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc (n : ℝ≥0) (min ((n : ℝ≥0) + 1) U),
        L < radiusInverseAngle a s ω} ≤ ENNReal.ofReal (angleEnvelopeConstant κ z / L)
  by_cases hnU : (n : ℝ≥0) ≤ U
  · by_cases hn : n = 0
    · subst n
      have hh := initial_inverse_angle_window_bound hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hε hεlim
        (min 1 U) U (min_le_left _ _) (min_le_right _ _) M hM
      simpa only [L, Nat.cast_zero, zero_add, mul_zero, Real.exp_zero, mul_one, angleEnvelopeConstant] using
        hh.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (le_max_left _ _) hM.le))
    · have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hvw : (n : ℝ≥0) ≤ min ((n : ℝ≥0) + 1) U := le_min (by simp) hnU
      have hh := inverse_angle_window_bound hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hε hεlim
        n (min ((n : ℝ≥0) + 1) U) U hn1 hvw (min_le_right _ _) L hL
      apply hh.trans
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ hL.le
      apply le_trans _ (le_max_right _ _)
      apply mul_le_mul_of_nonneg_left _ (uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)).le
      apply Real.exp_le_exp.mpr
      have hm : ((min (n + 1) U : ℝ≥0) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast min_le_left ((n : ℝ≥0) + 1) U
      have hd : (↑(min ((n : ℝ≥0) + 1) U) : ℝ) - (n : ℝ) ≤ 1 := by linarith
      simpa only [mul_one, NNReal.coe_natCast] using
        mul_le_mul_of_nonneg_left hd (codimension_pos κ hκ8).le
  · have hempty : {ω | localizedRadiusStop (a U) ω < ⊤ ∧
        ∃ s ∈ Icc (n : ℝ≥0) (min ((n : ℝ≥0) + 1) U), L < radiusInverseAngle a s ω} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨_, s, hs, _⟩
      exact hnU (hs.1.trans (hs.2.trans (min_le_right _ _)))
    change finiteCenteredLaw P κ B γ G z U _ ≤ _
    rw [hempty, measure_empty]
    exact bot_le

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma log_height_clock_derivative_nonpos
    (κ : ℝ) (q : ℂ × ℝ) (b : ℝ) :
    -2 / greenLogNormSq κ q b + logClockRate κ q b / 2 ≤ 0 := by
  have hh := mul_le_mul_of_nonneg_left (logAngleSq_le_one κ q b)
    (show (0 : ℝ) ≤ 2 / greenLogNormSq κ q b from
      div_nonneg (by norm_num) (greenLogNormSq_pos κ q b).le)
  have he : logClockRate κ q b / 2 = (2 / greenLogNormSq κ q b) * logAngleSq κ q b := by
    unfold logClockRate logAngleSq
    field_simp
    ring
  rw [he, neg_div]
  linarith

lemma log_loewner_radius_height_decay
    {Q : ℝ → ℂ × ℝ} {B : ℝ → ℝ} {κ T : ℝ}
    (hT : 0 ≤ T) (hQ0 : (Q 0).2 = 0)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (physicalLogLoewnerField (Real.sqrt κ * B t) (Q t)) (Icc 0 T) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (Q t).1.im ≤ (Q 0).1.im - logRadiusClock (Q 0).1.im (Q t) / 2 := by
  let η₀ := (Q 0).1.im
  have hQc : ContinuousOn Q (Icc 0 T) := fun t ht => (hQ t ht).continuousWithinAt
  have hSc : ContinuousOn (fun t => logRadiusClock η₀ (Q t)) (Icc 0 T) :=
    (continuous_logRadiusClock η₀).comp_continuousOn hQc
  have hanti : AntitoneOn (fun t => (Q t).1.im + logRadiusClock η₀ (Q t) / 2) (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      ((Complex.continuous_im.comp_continuousOn (continuous_fst.comp_continuousOn hQc)).add
        (hSc.div_const _))
      (fun t ht => ((log_ode_im_derivative (hQ t (interior_subset ht))).add
        ((log_ode_clock_derivative η₀ (hQ t (interior_subset ht))).div_const _)).mono interior_subset)
    intro t ht
    exact log_height_clock_derivative_nonpos κ (Q t) (B t)
  have hh := hanti (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht ht.1
  have hS0 : logRadiusClock η₀ (Q 0) = 0 := by simp [logRadiusClock, η₀, hQ0]
  dsimp only at hh
  rw [hS0, zero_div, add_zero] at hh
  change (Q t).1.im ≤ η₀ - _
  linarith

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ} (a : AngularLocalization B hm κ z u ε)

lemma physical_derivative (ω : Ω) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ)) :
    HasDerivWithinAt (fun t => a.solution.Q t ω)
      (physicalLogLoewnerField (Real.sqrt κ * B t.toNNReal ω) (a.solution.Q t ω))
        (Icc (0 : ℝ) (a.τ ω : ℝ)) t := by
  have hd := (a.solution.derivative ω t ht.1).mono
    (show Icc (0 : ℝ) (a.τ ω : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hb := (a.inside ω t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2)).2.2
  rw [Real.coe_toNNReal t ht.1] at hb
  rwa [clippedLogLoewnerField_eq_physical _ _ _ _ _ hb] at hd

noncomputable def radiusPhysicalRate (s : ℝ) (ω : Ω) : ℝ :=
  Real.exp (2 * (a.solution.Q (a.clock.inverse s ω) ω).1.im) /
    (4 * logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω)
      (B (a.clock.inverse s ω).toNNReal ω) ^ 2)

lemma radiusPhysicalRate_continuous
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun s => a.radiusPhysicalRate s ω) := by
  have hQ := (a.solution.lipschitz ω).continuous.comp (a.clock.continuous_inverse ω)
  have hB := (hBc ω).comp (continuous_real_toNNReal.comp (a.clock.continuous_inverse ω))
  have hA := (continuous_logAngleSq κ).comp (hQ.prodMk hB)
  exact (Real.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_im.comp hQ.fst))).div (continuous_const.mul (hA.pow 2))
    (fun s => mul_ne_zero (by norm_num) (pow_ne_zero 2 (logAngleSq_pos _ _ _).ne'))

lemma radiusPhysicalRate_at_clock (ω : Ω) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (a.τ ω : ℝ)) :
    a.radiusPhysicalRate (a.clock.S t ω) ω *
      logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω) = 1 := by
  unfold radiusPhysicalRate
  rw [a.clock.inverse_clock ω t ht, logClockRate_angle]
  have hA := (logAngleSq_pos κ (a.solution.Q t ω) (B t.toNNReal ω)).ne'
  have hE := Real.exp_ne_zero (2 * (a.solution.Q t ω).1.im)
  field_simp

lemma radiusPhysicalRate_integral
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    (∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), a.radiusPhysicalRate s ω) = (a.τ ω : ℝ) := by
  have hh := intervalIntegral.integral_comp_mul_deriv''
    (a.clock.continuous ω).continuousOn
    (f' := fun t => logClockRate κ (a.solution.Q t ω) (B t.toNNReal ω))
    (a := (0 : ℝ)) (b := (a.τ ω : ℝ)) (g := fun s => a.radiusPhysicalRate s ω)
    (fun t ht => by
      have ht' : t ∈ Ioo (0 : ℝ) (a.τ ω : ℝ) := by
        simpa only [min_eq_left (a.τ ω).coe_nonneg, max_eq_right (a.τ ω).coe_nonneg] using ht
      exact ((a.radius_clock_derivative ω t ⟨ht'.1.le, ht'.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)).hasDerivWithinAt)
    ((continuous_logClockRate κ).comp
      ((a.solution.lipschitz ω).continuous.prodMk
        ((hBc ω).comp continuous_real_toNNReal))).continuousOn
    (a.radiusPhysicalRate_continuous hBc ω).continuousOn
  rw [a.clock.zero ω] at hh
  rw [← hh]
  trans ∫ t in (0 : ℝ)..(a.τ ω : ℝ), (1 : ℝ)
  · apply intervalIntegral.integral_congr
    intro t ht
    exact a.radiusPhysicalRate_at_clock ω t (by simpa only [uIcc_of_le (a.τ ω).coe_nonneg] using ht)
  · simp

lemma radius_height_decay (ω : Ω) (s : ℝ) (hs : 0 ≤ s)
    (hsl : s ≤ a.clock.S (a.τ ω) ω) :
    (a.solution.Q (a.clock.inverse s ω) ω).1.im ≤ Real.log z.im - s / 2 := by
  have hh := log_loewner_radius_height_decay (a.τ ω).coe_nonneg
    (show (a.solution.Q 0 ω).2 = 0 by rw [a.solution.initial]; rfl)
    (a.physical_derivative ω) (a.clock.inverse s ω) (a.clock.inverse_mem s ω)
  have he := a.clock.clock_inverse s ω
  change logRadiusClock (Real.log z.im) (a.solution.Q (a.clock.inverse s ω) ω) =
    min (max s 0) (a.clock.S (a.τ ω) ω) at he
  rw [max_eq_left hs, min_eq_left hsl] at he
  have hinit : (a.solution.Q 0 ω).1.im = Real.log z.im := by
    rw [a.solution.initial, initialLogCoordinates_im]
  rwa [hinit, he] at hh

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma inverse_angle_control_rate {A a M s : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hM : 0 < M)
    (hV : A ^ (-a / 2) ≤ M * Real.exp (a * s / 8)) :
    1 / A ^ 2 ≤ M ^ (4 / a) * Real.exp (s / 2) := by
  have hp : 0 ≤ 4 / a := by positivity
  have hh := Real.rpow_le_rpow (Real.rpow_pos_of_pos hA _).le hV hp
  rw [← Real.rpow_mul hA.le] at hh
  have he : (-a / 2) * (4 / a) = -2 := by field_simp; ring
  rw [he, Real.rpow_neg hA.le, Real.rpow_two,
    Real.mul_rpow hM.le (Real.exp_pos _).le, ← Real.exp_mul] at hh
  have he' : a * s / 8 * (4 / a) = s / 2 := by field_simp; ring
  rw [he'] at hh
  simpa only [one_div] using hh

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ} (a : AngularLocalization B hm κ z u ε)

lemma physical_rate_of_envelope (hκ : 0 < κ) (hκ8 : κ < 8)
    (M : ℝ) (hM : 0 < M) (ω : Ω) (s : ℝ) (hs : 0 ≤ s)
    (hsl : s ≤ a.clock.S (a.τ ω) ω)
    (hV : (logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω)
      (B (a.clock.inverse s ω).toNNReal ω)) ^ (-greenExponent κ / 2) ≤
        M * Real.exp (greenExponent κ * s / 8)) :
    a.radiusPhysicalRate s ω ≤
      (Real.exp (2 * Real.log z.im) / 4 * M ^ (4 / greenExponent κ)) * Real.exp (-s / 2) := by
  let A := logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω)
    (B (a.clock.inverse s ω).toNNReal ω)
  have hA : 0 < A := logAngleSq_pos _ _ _
  have hp := inverse_angle_control_rate hA (greenExponent_pos κ hκ hκ8) hM hV
  have he : Real.exp (2 * (a.solution.Q (a.clock.inverse s ω) ω).1.im) ≤
      Real.exp (2 * Real.log z.im) * Real.exp (-s) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [a.radius_height_decay ω s hs hsl]
  unfold radiusPhysicalRate
  change Real.exp _ / (4 * A ^ 2) ≤ _
  calc
    _ = (Real.exp (2 * (a.solution.Q (a.clock.inverse s ω) ω).1.im) / 4) * (1 / A ^ 2) := by ring
    _ ≤ (Real.exp (2 * Real.log z.im) * Real.exp (-s) / 4) *
        (M ^ (4 / greenExponent κ) * Real.exp (s / 2)) :=
      mul_le_mul (div_le_div_of_nonneg_right he (by norm_num)) hp (by positivity) (by positivity)
    _ = _ := by
      rw [show Real.exp (2 * Real.log z.im) * Real.exp (-s) / 4 *
          (M ^ (4 / greenExponent κ) * Real.exp (s / 2)) =
          (Real.exp (2 * Real.log z.im) / 4 * M ^ (4 / greenExponent κ)) *
            (Real.exp (-s) * Real.exp (s / 2)) by ring, ← Real.exp_add]
      congr 2
      ring

end AngularLocalization
end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def physicalTimeThreshold (κ : ℝ) (z : ℂ) (M : ℝ) : ℝ :=
  Real.exp (2 * Real.log z.im) / 2 * M ^ (4 / greenExponent κ)

lemma physicalTimeThreshold_pos (κ : ℝ) (z : ℂ) {M : ℝ} (hM : 0 < M) :
    0 < physicalTimeThreshold κ z M :=
  mul_pos (div_pos (Real.exp_pos _) (by norm_num)) (Real.rpow_pos_of_pos hM _)

namespace AngularLocalization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u ε : ℝ} (a : AngularLocalization B hm κ z u ε)

lemma physical_time_of_envelope (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (M : ℝ) (hM : 0 < M) (ω : Ω)
    (hV : ∀ s ∈ Icc 0 (a.clock.S (a.τ ω) ω),
      (logAngleSq κ (a.solution.Q (a.clock.inverse s ω) ω)
        (B (a.clock.inverse s ω).toNNReal ω)) ^ (-greenExponent κ / 2) ≤
          M * Real.exp (greenExponent κ * s / 8)) :
    (a.τ ω : ℝ) ≤ physicalTimeThreshold κ z M := by
  let C := Real.exp (2 * Real.log z.im) / 4 * M ^ (4 / greenExponent κ)
  have hC : 0 ≤ C := mul_nonneg (div_nonneg (Real.exp_pos _).le (by norm_num))
    (Real.rpow_pos_of_pos hM _).le
  rw [← a.radiusPhysicalRate_integral hBc ω]
  calc
    _ ≤ ∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), C * Real.exp (-s / 2) := by
      apply intervalIntegral.integral_mono_on (a.clock.terminal_nonneg ω)
        ((a.radiusPhysicalRate_continuous hBc ω).intervalIntegrable _ _)
        ((continuous_const.mul (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).intervalIntegrable _ _)
      intro s hs
      exact a.physical_rate_of_envelope hκ hκ8 M hM ω s hs.1 hs.2 (hV s hs)
    _ = C * (∫ s in (0 : ℝ)..(a.clock.S (a.τ ω) ω), Real.exp (-s / 2)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left (integral_exp_neg_half_le_two _) hC
    _ = _ := by dsimp [C, physicalTimeThreshold]; ring

end AngularLocalization

lemma localized_physical_time_of_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ : ℝ} {z : ℂ} {ε : ℕ → ℝ}
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (U : ℝ≥0) (M : ℝ) (hM : 0 < M)
    (ω : Ω) (hω : localizedRadiusStop (a U) ω < ⊤)
    (hV : ∀ s ∈ Icc 0 U, radiusInverseAngle a s ω ≤ M * Real.exp (greenExponent κ / 8 * s)) :
    localizedRadiusStop (a U) ω ≤ ((physicalTimeThreshold κ z M).toNNReal : WithTop ℝ≥0) := by
  obtain ⟨n, hn⟩ := exists_cutoff_of_radiusStop_lt_top (a U) ω hω
  rw [localizedRadiusStop_eq_hit (a U) ω n hn, WithTop.coe_le_coe, ← NNReal.coe_le_coe,
    Real.coe_toNNReal _ (physicalTimeThreshold_pos κ z hM).le]
  apply (a U n).physical_time_of_envelope hBc hκ hκ8 M hM ω
  intro s hs
  have hsu : s ≤ (U : ℝ) := hs.2.trans_eq hn
  have hh := hV s.toNNReal ⟨bot_le, Real.toNNReal_le_iff_le_coe.mpr hsu⟩
  unfold radiusInverseAngle at hh
  rw [limitRadiusKernel_eq_below (a s.toNNReal) (a U) hε
    (by simpa only [Real.coe_toNNReal s hs.1] using hsu) 0 2 s.toNNReal
    s.toNNReal.coe_nonneg le_rfl ω, Real.coe_toNNReal s hs.1,
    limitRadiusKernel_eq_of_surviving_cutoff (a U) hε 0 2 s hs.1 ω n hs.2] at hh
  unfold AngularLocalization.radiusValue at hh
  rw [powerLogDensity_radius_angle κ 0 2 (Real.log z.im)] at hh
  norm_num only [zero_mul, Real.exp_zero, one_mul, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one] at hh
  convert hh using 1
  congr 2
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma finite_physical_tail_of_localizations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    {z : ℂ} (hz : z ∈ upperHalfPlane) {ε : ℕ → ℝ}
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (U : ℝ≥0) (M : ℝ) (hM : 0 < M) :
    finiteCenteredLaw P κ B γ G z U
      {ω | ENNReal.ofReal (physicalTimeThreshold κ z M) < radiusLevelTime (γ ω) (G ω) z U} ≤
      ENNReal.ofReal (angleEnvelopeConstant κ z / M / (1 - Real.exp (-greenExponent κ / 8))) := by
  have hwQ : ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G z U, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω) :=
    (withDensity_absolutelyContinuous P _).ae_le hw
  have hs : {ω | ENNReal.ofReal (physicalTimeThreshold κ z M) < radiusLevelTime (γ ω) (G ω) z U} ≤ᵐ[finiteCenteredLaw P κ B γ G z U]
      {ω | localizedRadiusStop (a U) ω < ⊤ ∧ ∃ s ∈ Icc 0 U,
        M * Real.exp (greenExponent κ / 8 * s) < radiusInverseAngle a s ω} := by
    filter_upwards [hwQ, finiteCenteredLaw_live_compact hB κ hκ hκ8 γ G F hw z hz U U.coe_nonneg] with ω hω hlive
    intro hlate
    have he := localizedRadiusStop_eq_source (a U) hεlim hBc hz ω (γ ω) (G ω) (F ω) hω
    obtain ⟨T, _, _, hT, _⟩ := hlive
    have hl : localizedRadiusStop (a U) ω < ⊤ := by rw [he, hT]; exact ENNReal.coe_lt_top
    refine ⟨hl, ?_⟩
    by_contra h
    push Not at h
    have hb := localized_physical_time_of_envelope a hε hBc hκ hκ8 U M hM ω hl h
    rw [he] at hb
    exact not_lt_of_ge hb hlate
  exact (measure_mono_ae hs).trans
    (finite_inverse_angle_envelope hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hε hεlim U M hM)

lemma finite_physical_tail_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (U : ℝ≥0) (M : ℝ) (hM : 0 < M) :
    finiteCenteredLaw P κ B γ G z U
      {ω | ENNReal.ofReal (physicalTimeThreshold κ z M) < radiusLevelTime (γ ω) (G ω) z U} ≤
      ENNReal.ofReal (angleEnvelopeConstant κ z / M / (1 - Real.exp (-greenExponent κ / 8))) := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := by
    dsimp [ε]
    exact div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (u : ℝ≥0) (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε n)
      u.coe_nonneg (hε0 n) (hεA n))
  exact finite_physical_tail_of_localizations hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hεanti hεlim U M hM

 

theorem finite_physical_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (U : ℝ≥0) (M : ℝ) (hM : 0 < M) :
    finiteCenteredLaw P κ B γ G z U
      {ω | ENNReal.ofReal (physicalTimeThreshold κ z M) < radiusLevelTime (γ ω) (G ω) z U} ≤
      ENNReal.ofReal (angleEnvelopeConstant κ z / M / (1 - Real.exp (-greenExponent κ / 8))) := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω he
    simpa only [he] using hω
  have hh := finite_physical_tail_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz U M hM
  rwa [finiteCenteredLaw_congr_driver hCB κ γ G z U] at hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem finite_physical_clock_tight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : ℝ≥0, 0 < T ∧ ∀ U : ℝ≥0,
      finiteCenteredLaw P κ B γ G z U
        {ω | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z U} ≤ ENNReal.ofReal δ := by
  let D := 1 - Real.exp (-greenExponent κ / 8)
  have hD : 0 < D := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (greenExponent_pos κ hκ hκ8)) (by norm_num)
  let M := angleEnvelopeConstant κ z / (δ * D)
  have hM : 0 < M := div_pos (angleEnvelopeConstant_pos κ z hz) (mul_pos hδ hD)
  refine ⟨(physicalTimeThreshold κ z M).toNNReal, Real.toNNReal_pos.mpr (physicalTimeThreshold_pos κ z hM), ?_⟩
  intro U
  have hh := finite_physical_tail hB κ hκ hκ8 γ G F hw z hz U M hM
  have he : angleEnvelopeConstant κ z / M / D = δ := by
    dsimp [M]
    field_simp [(angleEnvelopeConstant_pos κ z hz).ne', hD.ne', hδ.ne']
  change _ ≤ ENNReal.ofReal (angleEnvelopeConstant κ z / M / D) at hh
  rw [he] at hh
  exact hh

 

theorem finite_physical_clock_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    ∃ T : ℝ≥0, 0 < T ∧ ∀ U : ℝ≥0, (1 / 2 : ℝ≥0∞) ≤
      finiteCenteredLaw P κ B γ G z U
        {ω | radiusLevelTime (γ ω) (G ω) z U ≤ T} := by
  obtain ⟨T, hT, ht⟩ := finite_physical_clock_tight hB κ hκ hκ8 γ G F hw z hz (1/2) (by norm_num)
  refine ⟨T, hT, fun U => ?_⟩
  let Q := finiteCenteredLaw P κ B γ G z U
  let : IsProbabilityMeasure Q := finiteCenteredLaw_probability hB κ hκ hκ8 γ G F hw z hz U U.coe_nonneg
  have hu : {ω | radiusLevelTime (γ ω) (G ω) z U ≤ T} ∪
      {ω | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z U} = univ := by
    ext ω
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_or_gt _ _
  have hbad : Q {ω | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z U} ≤ (1 / 2 : ℝ≥0∞) := by
    have he : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [← he]
    exact ht U
  have hh : (1 : ℝ≥0∞) ≤ Q {ω | radiusLevelTime (γ ω) (G ω) z U ≤ T} + 1 / 2 := by
    have hsum := measure_union_le (μ := Q)
      {ω | radiusLevelTime (γ ω) (G ω) z U ≤ T}
      {ω | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (G ω) z U}
    rw [hu, measure_univ] at hsum
    exact hsum.trans (add_le_add le_rfl hbad)
  have hsub := tsub_le_iff_right.mpr hh
  norm_num at hsub
  simpa only [one_div] using hsub

end SLEExactGauge
end

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def finiteSpatialGreenMass (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (r : ℝ) (T : ℝ≥0) (K : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in K, ENNReal.ofReal (if spatialHitTime γ z r ≤ T then
    spatialGreenWeight κ U γ G z r else 0)
def SourceFiniteTimeFirstMomentTarget : Prop :=
  ∀ (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ γ : Ω → ℝ≥0 → ℂ, ∀ a : RegularSLEPresentation P κ γ,
  ∀ z₀ : ℂ, ∀ R : ℝ, 0 < R → closedBall z₀ R ⊆ upperHalfPlane →
  ∃ (T : ℝ≥0) (e₀ m₀ : ℝ), 0 < T ∧ 0 < e₀ ∧ 0 < m₀ ∧
    ∀ r : ℝ, 0 < r → r ≤ e₀ →
      ENNReal.ofReal m₀ ≤ ∫⁻ ω : a.samples,
        finiteSpatialGreenMass κ (fun t => Real.sqrt κ * a.B t ω)
          (γ ω) (a.G ω) r T (closedBall z₀ R) ∂(P.comap Subtype.val)

lemma initialGreen_continuousOn (κ : ℝ) : ContinuousOn (initialGreen κ) upperHalfPlane := by
  have hn (z : ℂ) (hz : z ∈ upperHalfPlane) : ‖z‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    intro he
    subst z
    exact (lt_irrefl 0) (show (0 : ℝ) < 0 from hz)
  have hy : ContinuousOn (fun z : ℂ => z.im) upperHalfPlane :=
    Complex.continuous_im.continuousOn
  have h1 := (hy.const_mul 2).rpow_const (p := -codimension κ)
    (fun z hz => Or.inl (mul_ne_zero (by norm_num) (ne_of_gt hz)))
  have h2 := (hy.div continuous_norm.continuousOn hn).rpow_const (p := greenExponent κ)
    (fun z hz => Or.inl (div_ne_zero (ne_of_gt hz) (hn z hz)))
  convert h1.mul h2 using 1
  funext z
  simp only [initialGreen, Complex.sin_arg, Pi.mul_apply, Pi.div_apply]

lemma angleEnvelopeConstant_continuousOn (κ : ℝ) :
    ContinuousOn (angleEnvelopeConstant κ) upperHalfPlane := by
  have hl : ContinuousOn (fun z : ℂ => Real.log z.im) upperHalfPlane :=
    Complex.continuous_im.continuousOn.log (fun _ hz => ne_of_gt hz)
  have he : ContinuousOn (fun z : ℂ => Real.exp
      (codimension κ * (1 - Real.log 2 - Real.log z.im))) upperHalfPlane :=
    Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.sub hl).const_mul (codimension κ))
  exact (he.div (initialGreen_continuousOn κ)
    (fun z hz => (initialGreen_pos κ z hz).ne')).sup continuousOn_const

noncomputable def halfClockThreshold (κ : ℝ) (z : ℂ) : ℝ :=
  physicalTimeThreshold κ z
    (angleEnvelopeConstant κ z / ((1 / 2) * (1 - Real.exp (-greenExponent κ / 8))))

lemma halfClockThreshold_pos {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : 0 < halfClockThreshold κ z := by
  apply physicalTimeThreshold_pos
  apply div_pos (angleEnvelopeConstant_pos κ z hz)
  apply mul_pos (by norm_num)
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by
    have := greenExponent_pos κ hκ hκ8
    linarith))

lemma halfClockThreshold_continuousOn {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ContinuousOn (halfClockThreshold κ) upperHalfPlane := by
  have hD : 0 < (1 / 2 : ℝ) * (1 - Real.exp (-greenExponent κ / 8)) := by
    apply mul_pos (by norm_num)
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by
      have := greenExponent_pos κ hκ hκ8
      linarith))
  have hM := (angleEnvelopeConstant_continuousOn κ).div_const
    ((1 / 2) * (1 - Real.exp (-greenExponent κ / 8)))
  have hp := hM.rpow_const (p := 4 / greenExponent κ) (fun z hz =>
    Or.inl (div_pos (angleEnvelopeConstant_pos κ z hz) hD).ne')
  have hl := Complex.continuous_im.continuousOn.log
    (s := upperHalfPlane) (fun _ hz => ne_of_gt hz)
  exact ((Real.continuous_exp.comp_continuousOn (hl.const_mul 2)).div_const 2).mul hp
namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialHitTime_stopping (z : ℂ) (r : ℝ) :
    IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
  a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r

 

lemma finite_spatial_density_identity [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r) (T : ℝ≥0) :
    (∫ ω : a.samples in {ω | spatialHitTime (γ ω) z r ≤ T},
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) z r ∂(P.comap Subtype.val)) =
    ∫ ω : a.samples in {ω | spatialHitTime (γ ω) z r ≤ T},
      stoppedGreen κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) z u ∂(P.comap Subtype.val) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  let σ (ω : a.samples) : ℝ≥0 := boundedSpatialHit (γ ω) z r T
  have hσ : IsStoppingTime a.filtration (fun ω => (σ ω : WithTop ℝ≥0)) :=
    a.boundedSpatialHit_stopping z r T
  let A := {ω : a.samples | spatialHitTime (γ ω) z r ≤ T}
  have hA : MeasurableSet[hσ.measurableSpace] A := by
    have hh := (a.spatialHitTime_stopping z r).measurableSet_stopping_time_le_min
      (isStoppingTime_const a.filtration T)
    rw [hσ.measurableSet]
    rw [IsStoppingTime.measurableSet] at hh
    simpa only [σ, A, boundedSpatialHit_coe] using hh
  have hAm : MeasurableSet A := hσ.measurableSpace_le _ hA
  have hWA : (fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) =ᵐ[μ.restrict A]
      fun ω => M (σ ω) ω := by
    filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem hAm] with ω he hω
    change spatialHitTime (γ ω) z r ≤ (T : WithTop ℝ≥0) at hω
    rw [he.1]
    simp only [Function.comp_apply]
    rw [(a.witness ω).physicalGreen_eq_before_spatial
      ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel (σ ω)
      (boundedSpatialHit_le (γ ω) z r T)]
    have hn : spatialHitTime (γ ω) z r ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hω
    simp only [spatialGreenWeight, ite_eq_right hn, σ, boundedSpatialHit,
      min_eq_left hω]
  calc
    _ = ∫ ω in A, M (σ ω) ω ∂μ := integral_congr_ae hWA
    _ = ∫ ω in A, μ[Z | hσ.measurableSpace] ω ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hStop σ hσ))
    _ = ∫ ω in A, Z ω ∂μ := setIntegral_condExp hσ.measurableSpace_le hZ hA
    _ = _ := integral_congr_ae (ae_restrict_of_ae (heq.mono fun ω hω => hω.2))

lemma finite_spatial_lintegral_identity [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r) (T : ℝ≥0) :
    (∫⁻ ω : a.samples, ENNReal.ofReal (if spatialHitTime (γ ω) z r ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) z r else 0) ∂(P.comap Subtype.val)) =
    ENNReal.ofReal (initialGreen κ z) *
      finiteCenteredLaw (P.comap Subtype.val) κ a.B (γ ∘ Subtype.val) a.G z u
        {ω | spatialHitTime (γ ω) z r ≤ T} := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let A := {ω : a.samples | spatialHitTime (γ ω) z r ≤ T}
  have hA : MeasurableSet A :=
    (a.spatialHitTime_stopping z r).measurableSpace_le _
      ((a.spatialHitTime_stopping z r).measurableSet_le' T)
  have hi := (a.spatialGreen_expectation hκ hκ8 z r hr hy).1.integrableOn (s := A)
  have hn : 0 ≤ᵐ[μ.restrict A] (fun ω : a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) :=
    Eventually.of_forall fun ω => by
      dsimp only [Pi.zero_apply, spatialGreenWeight]
      split_ifs
      · exact le_rfl
      · exact greenDensity_nonneg (a.witness ω) κ _ z
  have hind (ω : a.samples) : ENNReal.ofReal (if spatialHitTime (γ ω) z r ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r else 0) =
      A.indicator (fun ω : a.samples => ENNReal.ofReal (spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r)) ω := by
    dsimp only [A, Set.indicator, mem_ofPred_eq]
    split_ifs <;> simp_all only [ENNReal.ofReal_zero]
  simp_rw [hind]
  rw [lintegral_indicator hA, ← ofReal_integral_eq_lintegral_ofReal hi hn,
    a.finite_spatial_density_identity hκ hκ8 z hz r hr hy u hu hlevel T,
    finiteCenteredLaw_apply a.brownian κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F
      (Eventually.of_forall a.witness) z hz u hu A hA,
    ← ENNReal.ofReal_mul (initialGreen_pos κ z hz).le]
  congr 1
  simp only [Function.comp_apply]
  field_simp [(initialGreen_pos κ z hz).ne']
  rfl

lemma finite_spatial_lintegral_lower [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8) (z : ℂ) (hz : z ∈ upperHalfPlane)
    (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (T : ℝ≥0) (hT : halfClockThreshold κ z ≤ T) :
    ENNReal.ofReal (initialGreen κ z / 2) ≤
      ∫⁻ ω : a.samples, ENNReal.ofReal (if spatialHitTime (γ ω) z r ≤ T then
        spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
          (γ ω) (a.G ω) z r else 0) ∂(P.comap Subtype.val) := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  let u := Real.log (4 * z.im / r)
  have hratio : 0 < 4 * z.im / r := div_pos (mul_pos (by norm_num) hz) hr
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hr).mpr (by linarith))
  have hlev : (2 * z.im) * Real.exp (-u) < r := by
    have he : (2 * z.im) * Real.exp (-u) = r / 2 := by
      dsimp only [u]
      rw [Real.exp_neg, Real.exp_log hratio]
      field_simp [(show 0 < z.im from hz).ne']
      ring
    rw [he]
    linarith
  let Q := finiteCenteredLaw μ κ a.B (γ ∘ Subtype.val) a.G z u
  let : IsProbabilityMeasure Q := finiteCenteredLaw_probability a.brownian κ hκ hκ8
    (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  let D := 1 - Real.exp (-greenExponent κ / 8)
  have hD : 0 < D := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    have := greenExponent_pos κ hκ hκ8
    linarith
  let M := angleEnvelopeConstant κ z / ((1 / 2) * D)
  have hM : 0 < M := div_pos (angleEnvelopeConstant_pos κ z hz) (mul_pos (by norm_num) hD)
  have hbad : Q {ω | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (a.G ω) z u} ≤ 1 / 2 := by
    have hh := finite_physical_tail a.brownian κ hκ hκ8 (γ ∘ Subtype.val)
      a.G a.F (Eventually.of_forall a.witness) z hz ⟨u, hu⟩ M hM
    have he : angleEnvelopeConstant κ z / M / D = 1 / 2 := by
      dsimp only [M]
      field_simp [(angleEnvelopeConstant_pos κ z hz).ne', hD.ne']
    change Q {ω | ENNReal.ofReal (halfClockThreshold κ z) <
      radiusLevelTime (γ ω) (a.G ω) z u} ≤ ENNReal.ofReal (angleEnvelopeConstant κ z / M / D) at hh
    rw [he] at hh
    have hTT : ENNReal.ofReal (halfClockThreshold κ z) ≤ (T : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hT
    have hhalf : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hhalf] at hh
    exact (measure_mono (fun ω hω => hTT.trans_lt hω)).trans hh
  have hgood : (1 / 2 : ℝ≥0∞) ≤ Q {ω | radiusLevelTime (γ ω) (a.G ω) z u ≤ T} := by
    have he : {ω : a.samples | radiusLevelTime (γ ω) (a.G ω) z u ≤ T} ∪
        {ω | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (a.G ω) z u} = univ := by
      ext ω
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact le_or_gt _ _
    have hh : (1 : ℝ≥0∞) ≤ Q {ω | radiusLevelTime (γ ω) (a.G ω) z u ≤ T} + 1 / 2 := by
      have hs := measure_union_le (μ := Q)
        {ω : a.samples | radiusLevelTime (γ ω) (a.G ω) z u ≤ T}
        {ω : a.samples | (T : ℝ≥0∞) < radiusLevelTime (γ ω) (a.G ω) z u}
      rw [he, measure_univ] at hs
      exact hs.trans (add_le_add le_rfl hbad)
    have hh' := tsub_le_iff_right.mpr hh
    norm_num at hh'
    simpa only [one_div] using hh'
  have hhit : (1 / 2 : ℝ≥0∞) ≤ Q {ω | spatialHitTime (γ ω) z r ≤ T} := by
    apply hgood.trans (measure_mono _)
    intro ω hω
    exact ((a.witness ω).radius_hit_forces_spatial_before
      ((a.continuous_B ω).const_mul _) z r hr hy u hlev T hω).le
  rw [a.finite_spatial_lintegral_identity hκ hκ8 z hz r hr hy u hu hlev T]
  calc
    _ = ENNReal.ofReal (initialGreen κ z) * (1 / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul' le_rfl hhit

lemma finiteSpatialGreenMass_expectation_swap [IsProbabilityMeasure P] (r : ℝ) (T : ℝ≥0) (K : Set ℂ) :
    (∫⁻ ω : a.samples, finiteSpatialGreenMass κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) r T K ∂(P.comap Subtype.val)) =
    ∫⁻ z in K, ∫⁻ ω : a.samples, ENNReal.ofReal (if spatialHitTime (γ ω) z r ≤ T then
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) z r else 0) ∂(P.comap Subtype.val) := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hm (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have ht := spatialHitTime_measurable (fun ω : a.samples => γ ω) a.trace_continuous hm r
  have he : MeasurableSet {p : ℂ × a.samples | spatialHitTime (γ p.2) p.1 r ≤ T} :=
    measurableSet_le ht measurable_const
  classical
  have hW := (@Measurable.ite _ _ _ _ _ _ _ (fun _ => Classical.propDecidable _)
    he (a.spatialGreenWeight_measurable r) (measurable_const (a := (0 : ℝ)))).ennreal_ofReal
  symm
  apply lintegral_lintegral_swap
  convert hW.aemeasurable using 1
  ext ⟨z, ω⟩
  simp only [Function.uncurry_apply_pair]

 

theorem source_finite_time_first_moment [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8) (z₀ : ℂ) (R : ℝ)
    (hR : 0 < R) (hK : closedBall z₀ R ⊆ upperHalfPlane) :
    ∃ (T : ℝ≥0) (e₀ m₀ : ℝ), 0 < T ∧ 0 < e₀ ∧ 0 < m₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ e₀ →
        ENNReal.ofReal m₀ ≤ ∫⁻ ω : a.samples,
          finiteSpatialGreenMass κ (fun t => Real.sqrt κ * a.B t ω)
            (γ ω) (a.G ω) r T (closedBall z₀ R) ∂(P.comap Subtype.val) := by
  have hne : (closedBall z₀ R).Nonempty := ⟨z₀, mem_closedBall_self hR.le⟩
  obtain ⟨zy, hzy, hy⟩ := (isCompact_closedBall z₀ R).exists_isMinOn hne
    Complex.continuous_im.continuousOn
  obtain ⟨zg, hzg, hg⟩ := (isCompact_closedBall z₀ R).exists_isMinOn hne
    ((initialGreen_continuousOn κ).mono hK)
  obtain ⟨zt, hzt, ht⟩ := (isCompact_closedBall z₀ R).exists_isMaxOn hne
    ((halfClockThreshold_continuousOn hκ hκ8).mono hK)
  let T := (halfClockThreshold κ zt).toNNReal
  have hT : 0 < T := Real.toNNReal_pos.mpr (halfClockThreshold_pos hκ hκ8 (hK hzt))
  let m := initialGreen κ zg / 2
  have hm : 0 < m := div_pos (initialGreen_pos κ zg (hK hzg)) (by norm_num)
  have hvol : 0 < volume (closedBall z₀ R) := measure_closedBall_pos volume z₀ hR
  have hvolfin : volume (closedBall z₀ R) ≠ ⊤ := (isCompact_closedBall z₀ R).measure_ne_top
  refine ⟨T, zy.im, m * (volume (closedBall z₀ R)).toReal, hT, hK hzy,
    mul_pos hm (ENNReal.toReal_pos hvol.ne' hvolfin), ?_⟩
  intro r hr hre
  rw [a.finiteSpatialGreenMass_expectation_swap]
  calc
    _ = ENNReal.ofReal m * volume (closedBall z₀ R) := by
      rw [ENNReal.ofReal_mul hm.le, ENNReal.ofReal_toReal hvolfin]
    _ = ∫⁻ _z in closedBall z₀ R, ENNReal.ofReal m := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply setLIntegral_mono' isClosed_closedBall.measurableSet
      intro z hz
      apply (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hg hz) (by norm_num))).trans
      apply a.finite_spatial_lintegral_lower hκ hκ8 z (hK hz) r hr (hre.trans (hy hz)) T
      exact (ht hz).trans (Real.le_coe_toNNReal _)

end RegularSLEPresentation

theorem sourceFiniteTimeFirstMoment : SourceFiniteTimeFirstMomentTarget := by
  intro Ω mΩ P hP κ hκ hκ8 γ a z₀ R hR hK
  let : IsProbabilityMeasure P := hP
  exact a.source_finite_time_first_moment hκ hκ8 z₀ R hR hK

end SLEExactGauge
end

end OAI
