import Mathlib
import OAI.Probability.SLE.FiniteStoppedLaw

namespace OAI

/-! Occupation Bound for chordal SLE. -/

section
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma occupation_difference {F H : ℝ → ℝ} {v A C L : ℝ}
    (hv : 0 ≤ v) (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ s in (0 : ℝ)..u, H s) =
      L + A * (∫ s in (0 : ℝ)..u, F s))
    {s t : ℝ} (hs : s ∈ Icc 0 v) (ht : t ∈ Icc 0 v) :
    F t + C * (∫ u in s..t, H u) = F s + A * (∫ u in s..t, F u) := by
  have sub (x : ℝ) (hx : x ∈ Icc 0 v) : uIcc 0 x ⊆ uIcc 0 v := by
    simpa only [uIcc_of_le hx.1, uIcc_of_le hv] using Icc_subset_Icc le_rfl hx.2
  rw [← intervalIntegral.integral_interval_sub_left (hHi.mono_set (sub t ht)) (hHi.mono_set (sub s hs)),
    ← intervalIntegral.integral_interval_sub_left (hFi.mono_set (sub t ht)) (hFi.mono_set (sub s hs))]
  linarith [hbal s hs, hbal t ht]

lemma high_occupation_le {F H : ℝ → ℝ} {v A C L D s t : ℝ}
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hC : 0 < C)
    (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ x in (0 : ℝ)..u, H x) =
      L + A * (∫ x in (0 : ℝ)..u, F x))
    (hs : s ∈ Icc 0 v) (ht : t ∈ Icc 0 v) (hst : s ≤ t)
    (hn : 0 ≤ F t) (hb : ∀ x ∈ Icc s t, F x ≤ D) :
    (∫ x in s..t, H x) ≤ D * (1 + A * (t - s)) / C := by
  have sub : uIcc s t ⊆ uIcc 0 v := by
    simpa only [uIcc_of_le hst, uIcc_of_le hv] using Icc_subset_Icc hs.1 ht.2
  have hl : (∫ x in s..t, F x) ≤ (t - s) * D := by
    have h := intervalIntegral.integral_mono_on hst (hFi.mono_set sub) intervalIntegrable_const hb
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have he := occupation_difference hv hFi hHi hbal hs ht
  have hh := mul_le_mul_of_nonneg_left hl hA
  apply (le_div_iff₀ hC).mpr
  have hFs := hb s (left_mem_Icc.mpr hst)
  nlinarith

lemma point_le_occupation {H : ℝ → ℝ} {s t G Q : ℝ}
    (hst : s < t) (hi : IntervalIntegrable H volume s t)
    (hd : ∀ᵐ x ∂volume.restrict (Icc s t), G ≤ Q * H x) :
    G ≤ Q * (∫ x in s..t, H x) / (t - s) := by
  have hh := intervalIntegral.integral_mono_ae_restrict hst.le
    (intervalIntegrable_const (c := G)) (hi.const_mul Q) hd
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul] at hh
  exact (le_div_iff₀ (sub_pos.mpr hst)).mpr (by nlinarith)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

lemma radiusMoment_zero_growth
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (hκ8 : κ < 8)
    (hz : z ∈ upperHalfPlane) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    radiusMoment P c (greenExponent κ) t ≤ Real.exp (codimension κ * (t - s)) *
      radiusMoment P c (greenExponent κ) s := by
  have hh := div_le_div_of_nonneg_right
    (integral_limitRadiusKernel_zero_growth (P := P) c hε hBm (codimension κ) s t (codimension_pos κ hκ8).le hs hst)
    (initialGreen_pos κ z hz).le
  simpa only [radiusMoment, sub_self, mul_div_assoc] using hh

lemma radiusMoment_zero_le_high
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2)) (hκ8 : κ < 8)
    (hz : z ∈ upperHalfPlane) (b s : ℝ) (hb : greenExponent κ ≤ b + 2)
    (hh : Integrable (limitRadiusKernel c (codimension κ) (greenExponent κ - b - 2) s) P) :
    radiusMoment P c (greenExponent κ) s ≤ radiusMoment P c (b + 2) s := by
  apply div_le_div_of_nonneg_right _ (initialGreen_pos κ z hz).le
  rw [sub_self, sub_add_eq_sub_sub]
  apply integral_limitRadiusKernel_antitone_power c hε (codimension κ) (greenExponent κ - b - 2) 0 s
    (by linarith) hh
  exact limitRadiusKernel_integrable c hε hBm (codimension κ) 0 (codimension_pos κ hκ8).le le_rfl s

lemma radiusMoment_high_integrable
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    IntervalIntegrable (radiusMoment P (a v) (b + 2)) volume 0 v := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  apply radiusMoment_intervalIntegrable _ v.coe_nonneg
  simpa only [sub_add_eq_sub_sub] using
    (limit_power_balance (a v) (a v) hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb v.coe_nonneg le_rfl).1

lemma radiusMoment_high_occupation
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hηv : 2 * η ≤ (v : ℝ)) :
    (∫ s in (v : ℝ) - η..v, radiusMoment P (a v) (b + 2) s) ≤
      angularMomentBound κ b η * (1 + lyapunovA κ b * η) / lyapunovC κ b := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hFi := radiusMoment_intervalIntegrable (P := P) (a v) v.coe_nonneg
    (limitRadiusKernel_region_integrable (a v) hε hBm (codimension κ) (greenExponent κ - b)
      (codimension_pos κ hκ8).le (sub_pos.mpr hb).le v)
  have hHi := radiusMoment_high_integrable a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb (v := v)
  have hbal := radiusMoment_balance a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb (v := v)
  have hbound := radiusMoment_bound a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz b hb0 hb η hη hη1 (v := v)
  have hh := high_occupation_le v.coe_nonneg (lyapunovA_nonneg hκ hb0 hb) (lyapunovC_pos hκ hb0 hb)
    hFi hHi hbal (s := (v : ℝ) - η) (t := v) (D := angularMomentBound κ b η)
    (by constructor <;> linarith) ⟨v.coe_nonneg, le_rfl⟩ (by linarith)
    (radiusMoment_nonneg _ (initialGreen_pos κ z hz).le b v)
    (fun x hx => hbound x ⟨by linarith [hx.1], hx.2⟩)
  simpa only [sub_sub_cancel] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def inverseAngleBound (κ b η : ℝ) : ℝ :=
  Real.exp (codimension κ * η) *
    (angularMomentBound κ b η * (1 + lyapunovA κ b * η) / lyapunovC κ b) / η

lemma inverseAngleBound_pos {κ b η : ℝ} (hκ : 0 < κ) (hb0 : 0 < b)
    (hb : b < greenExponent κ) (hη : 0 < η) : 0 < inverseAngleBound κ b η := by
  have hD := angularMomentBound_pos hκ hb0 hb hη
  have hA := lyapunovA_nonneg hκ hb0 hb
  have hC := lyapunovC_pos hκ hb0 hb
  dsimp only [inverseAngleBound]
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

lemma radiusMoment_zero_growth_high_ae
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) (hb2 : greenExponent κ ≤ b + 2)
    (η : ℝ) (_hη : 0 < η) (hηv : η ≤ (v : ℝ)) :
    ∀ᵐ s ∂volume.restrict (Icc ((v : ℝ) - η) v),
      radiusMoment P (a v) (greenExponent κ) v ≤
        Real.exp (codimension κ * η) * radiusMoment P (a v) (b + 2) s := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hh := (limit_power_balance (a v) (a v) hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb v.coe_nonneg le_rfl).1.prod_right_ae
  rw [restrict_Ioc_eq_restrict_Icc] at hh
  have hs : Icc ((v : ℝ) - η) v ⊆ Icc 0 v := Icc_subset_Icc (by linarith) le_rfl
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hh, ae_restrict_mem measurableSet_Icc] with s hsi hsm
  have hs0 : 0 ≤ s := (hs hsm).1
  have hg := radiusMoment_zero_growth (a v) hε hBm hκ8 hz hs0 hsm.2 (P := P)
  have hdom := radiusMoment_zero_le_high (a v) hε hBm hκ8 hz b s hb2 hsi (P := P)
  have he : Real.exp (codimension κ * ((v : ℝ) - s)) ≤ Real.exp (codimension κ * η) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith [hsm.1]) (codimension_pos κ hκ8).le
  exact hg.trans ((mul_le_mul_of_nonneg_right he
    (radiusMoment_nonneg _ (initialGreen_pos κ z hz).le _ _)).trans
      (mul_le_mul_of_nonneg_left hdom (Real.exp_pos _).le))

 

theorem radiusMoment_inverseAngle_bound
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) (hb2 : greenExponent κ ≤ b + 2)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hηv : 2 * η ≤ (v : ℝ)) :
    radiusMoment P (a v) (greenExponent κ) v ≤ inverseAngleBound κ b η := by
  have hd := radiusMoment_zero_growth_high_ae a hε hεlim hε0 hB hBm hBc hB0
    hκ hκ8 hz b hb0 hb hb2 η hη (by linarith : η ≤ (v : ℝ))
  have hi := radiusMoment_high_integrable a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb (v := v)
  have his : IntervalIntegrable (radiusMoment P (a v) (b + 2)) volume ((v : ℝ) - η) v := by
    apply hi.mono_set
    simp only [uIcc_of_le (by linarith : (v : ℝ) - η ≤ v), uIcc_of_le v.coe_nonneg]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hp := point_le_occupation (by linarith : (v : ℝ) - η < v) his hd
  have hocc := radiusMoment_high_occupation a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz b hb0 hb η hη hη1 hηv
  simp only [sub_sub_cancel] at hp
  exact hp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hocc (Real.exp_pos _).le) hη.le)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  (hB : IsBrownianReal B P)
  (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
  (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
  {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
  (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
    (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
  {z : ℂ} (hz : z ∈ upperHalfPlane) {u v : ℝ} {ε : ℕ → ℝ}

include hB hBm hBc hB0 hκ hκ8 hw hz

lemma localization_integral_tendsto
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0)) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, (a n).weight ω ∂P) atTop
      (𝓝 (∫ ω in A, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u ∂P)) := by
  have hi (n : ℕ) := ((a n).mean_green hB hBm hBc hB0 hκ hκ8 hz).1
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)))
    (fun n => (hi n).integrableOn.aestronglyMeasurable) (integrable_const _)
  · intro n
    apply Eventually.of_forall
    intro ω
    change ‖(a n).weight ω‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg ((a n).weight_bound hκ hκ8 ω).1]
    exact ((a n).weight_bound hκ hκ8 ω).2
  · filter_upwards [ae_restrict_of_ae hw] with ω hω
    exact localization_weight_tendsto a hε hBc hκ hκ8 hz ω (γ ω) (G ω) (F ω) hω

omit hw hz [IsProbabilityMeasure P] in
lemma localization_history_finer
    {η δ : ℝ} (a : AngularLocalization B hm κ z u η)
    (b : AngularLocalization B hm κ z v δ) (huv : u ≤ v) (hδη : δ ≤ η)
    (A : Set Ω) (hA : MeasurableSet[a.stopping.measurableSpace] A) :
    (∫ ω in A, b.weight ω ∂P) = ∫ ω in A, a.weight ω ∂P := by
  have hle := a.stopping_le b huv hδη
  have he := b.solution.stopped_green_history hB hBm hBc hB0 hκ hκ8
    (Real.log z.im) v a.τ b.τ a.stopping b.stopping hle b.T b.bounded
    (fun ω t ht => ⟨(b.inside ω t ht).1, (b.inside ω t ht).2.2⟩) A hA
  refine he.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_))
  dsimp only
  rw [← a.synchronize b ω (a.τ ω) le_rfl (hle ω)]
  rfl

lemma finite_history_on_hit
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Tendsto ε atTop (𝓝 0)) (hεanti : Antitone ε) (huv : u ≤ v)
    (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[(localizedRadiusStop_stopping a).measurableSpace] A) :
    (∫ ω in A ∩ (a n).hit, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z v ∂P) =
      ∫ ω in A ∩ (a n).hit, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u ∂P := by
  have hAn := localizedRadiusStop_history_hit a n A hA
  have he (m : ℕ) := localization_history_finer hB hBm hBc hB0 hκ hκ8
    (a n) (b (m + n)) huv (hεanti (Nat.le_add_left n m)) (A ∩ (a n).hit) hAn
  have hlim := (localization_integral_tendsto hB hBm hBc hB0 hκ hκ8 γ G F hw hz b hε
    (A ∩ (a n).hit)).comp (tendsto_add_atTop_nat n)
  have hx : (∫ ω in A ∩ (a n).hit, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z v ∂P) = ∫ ω in A ∩ (a n).hit, (a n).weight ω ∂P := by
    apply tendsto_nhds_unique hlim
    simpa only [Function.comp_def, he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω in A ∩ (a n).hit, (a n).weight ω ∂P) atTop (𝓝 _))
  refine hx.trans (integral_congr_ae ?_)
  have hAnm : MeasurableSet (A ∩ (a n).hit) := (a n).stopping.measurableSpace_le _ hAn
  filter_upwards [ae_restrict_of_ae hw, ae_restrict_mem hAnm] with ω hω hωA
  exact (a n).weight_eq_stoppedGreen_of_hit hBc hz ω (γ ω) (G ω) (F ω) hω hωA.2

lemma hit_integral_tendsto
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Tendsto ε atTop (𝓝 0)) (hu : 0 ≤ u) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A ∩ (a n).hit, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u ∂P) atTop
      (𝓝 (∫ ω in A, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u ∂P)) := by
  let g (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u
  have hi := (finite_stopped_green_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz u hu).1
  have hhit (n : ℕ) : MeasurableSet (a n).hit := (a n).stopping.measurableSpace_le _ (a n).measurable_hit
  have hlim : Tendsto (fun n => ∫ ω in A, (a n).hit.indicator g ω ∂P) atTop (𝓝 (∫ ω in A, g ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => ‖g ω‖)
      (fun n => (hi.indicator (hhit n)).integrableOn.aestronglyMeasurable) hi.norm.integrableOn
    · intro n
      exact Eventually.of_forall fun ω => norm_indicator_le_norm_self _ _
    · filter_upwards [ae_restrict_of_ae hw] with ω hω
      change Tendsto (fun n => (a n).hit.indicator g ω) atTop (𝓝 (g ω))
      by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain (γ ω) T ∧
          fullRadius (G ω) T z = (2 * z.im) * Real.exp (-u)
      · obtain ⟨T, hT, hR⟩ := hh
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_hit_of_live_level a hε hBc hz ω (γ ω) (G ω) (F ω) hω T hT hR] with n hn
        simp only [Set.indicator_of_mem hn.1]
      · have hg : g ω = 0 := stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hh
        have he (n : ℕ) : (a n).hit.indicator g ω = 0 := by
          by_cases hn : ω ∈ (a n).hit <;> simp [hn, hg]
        simpa only [he, hg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa only [integral_indicator (hhit _), Measure.restrict_restrict (hhit _), Set.inter_comm] using hlim

 

theorem finite_stopped_green_consistent_regular
    (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (b : ∀ n, AngularLocalization B hm κ z v (ε n))
    (hε : Tendsto ε atTop (𝓝 0)) (hεanti : Antitone ε)
    (hu : 0 ≤ u) (huv : u ≤ v) (A : Set Ω)
    (hA : MeasurableSet[(localizedRadiusStop_stopping a).measurableSpace] A) :
    (∫ ω in A, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z v ∂P) =
      ∫ ω in A, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u ∂P := by
  let gu (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u
  let gv (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z v
  obtain ⟨hiu, heu⟩ := finite_stopped_green_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz u hu
  obtain ⟨hiv, hev⟩ := finite_stopped_green_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz v (hu.trans huv)
  have hgv : 0 ≤ᵐ[P] gv := hw.mono fun ω hω => stoppedGreen_nonneg hω κ z v
  have hmono (C : Set Ω) (hC : MeasurableSet[(localizedRadiusStop_stopping a).measurableSpace] C) :
      (∫ ω in C, gu ω ∂P) ≤ ∫ ω in C, gv ω ∂P := by
    have hlim := hit_integral_tendsto hB hBm hBc hB0 hκ hκ8 γ G F hw hz a hε hu C
    apply le_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    rw [← finite_history_on_hit hB hBm hBc hB0 hκ hκ8 γ G F hw hz a b hε hεanti huv n C hC]
    exact setIntegral_mono_set hiv.integrableOn (ae_restrict_of_ae hgv)
      (Eventually.of_forall fun ω hω => hω.1)
  have h1 := hmono A hA
  have h2 := hmono Aᶜ hA.compl
  have hAm : MeasurableSet A := (localizedRadiusStop_stopping a).measurableSpace_le _ hA
  have hsumu := integral_add_compl hAm hiu
  have hsumv := integral_add_compl hAm hiv
  change (∫ ω in A, gu ω ∂P) + (∫ ω in Aᶜ, gu ω ∂P) = _ at hsumu
  change (∫ ω in A, gv ω ∂P) + (∫ ω in Aᶜ, gv ω ∂P) = _ at hsumv
  rw [heu] at hsumu
  rw [hev] at hsumv
  change (∫ ω in A, gv ω ∂P) = ∫ ω in A, gu ω ∂P
  linarith

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma finiteCenteredLaw_apply
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u)
    (A : Set Ω) (hA : MeasurableSet A) :
    finiteCenteredLaw P κ B γ G z u A = ENNReal.ofReal
      ((∫ ω in A, stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u ∂P) /
        initialGreen κ z) := by
  have hi := (finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu).1
  rw [finiteCenteredLaw, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal ((hi.div_const _).integrableOn) ?_, integral_div]
  filter_upwards [ae_restrict_of_ae hw] with ω hω
  exact div_nonneg (stoppedGreen_nonneg hω κ z u) (initialGreen_pos κ z hz).le

 

theorem exists_consistent_finiteCenteredLaw_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    ∃ (ρ : ℝ≥0 → Ω → WithTop ℝ≥0)
      (hρ : ∀ u, IsStoppingTime (Filtration.natural B
        (fun _ => (hBm.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable)) (ρ u)),
      (∀ u, ∀ᵐ ω ∂P, ρ u ω = radiusLevelTime (γ ω) (G ω) z u) ∧
      (∀ (u : ℝ≥0), IsProbabilityMeasure (finiteCenteredLaw P κ B γ G z u)) ∧
      (∀ (u v : ℝ≥0), u ≤ v → ∀ A : Set Ω, MeasurableSet[(hρ u).measurableSpace] A →
        finiteCenteredLaw P κ B γ G z v A = finiteCenteredLaw P κ B γ G z u A) := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε₀ (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (u : ℝ≥0) (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε n)
      u.coe_nonneg (hε n) (hε₀ n))
  refine ⟨fun u => localizedRadiusStop (a u), fun u => localizedRadiusStop_stopping (a u), ?_, ?_, ?_⟩
  · intro u
    filter_upwards [hw] with ω hω
    exact localizedRadiusStop_eq_source (a u) hεlim hBc hz ω (γ ω) (G ω) (F ω) hω
  · intro u
    exact finiteCenteredLaw_probability hB κ hκ hκ8 γ G F hw z hz u u.coe_nonneg
  · intro u v huv A hA
    have hAm : MeasurableSet A := (localizedRadiusStop_stopping (a u)).measurableSpace_le _ hA
    rw [finiteCenteredLaw_apply hB κ hκ hκ8 γ G F hw z hz v v.coe_nonneg A hAm,
      finiteCenteredLaw_apply hB κ hκ hκ8 γ G F hw z hz u u.coe_nonneg A hAm,
      finite_stopped_green_consistent_regular hB hBm hBc hB0 hκ hκ8 γ G F hw hz
        (a u) (a v) hεlim hεanti u.coe_nonneg huv A hA]

lemma finiteCenteredLaw_congr_driver
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B C : ℝ≥0 → Ω → ℝ}
    (hCB : ∀ᵐ ω ∂P, ∀ t, C t ω = B t ω)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (z : ℂ) (u : ℝ) :
    finiteCenteredLaw P κ C γ G z u = finiteCenteredLaw P κ B γ G z u := by
  apply withDensity_congr_ae
  filter_upwards [hCB] with ω hω
  simp only [hω]

 

theorem exists_consistent_finiteCenteredLaw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) :
    ∃ (C : ℝ≥0 → Ω → ℝ) (hCm : ∀ t, Measurable (C t))
      (ρ : ℝ≥0 → Ω → WithTop ℝ≥0)
      (hρ : ∀ u, IsStoppingTime (Filtration.natural C (fun t => (hCm t).stronglyMeasurable)) (ρ u)),
      (∀ᵐ ω ∂P, ∀ t, C t ω = B t ω) ∧
      (∀ u, ∀ᵐ ω ∂P, ρ u ω = radiusLevelTime (γ ω) (G ω) z u) ∧
      (∀ (u : ℝ≥0), IsProbabilityMeasure (finiteCenteredLaw P κ B γ G z u)) ∧
      (∀ (u v : ℝ≥0), u ≤ v → ∀ A : Set Ω, MeasurableSet[(hρ u).measurableSpace] A →
        finiteCenteredLaw P κ B γ G z v A = finiteCenteredLaw P κ B γ G z u A) := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω he
    simpa only [he] using hω
  obtain ⟨ρ, hρ, hρeq, hprob, hcon⟩ := exists_consistent_finiteCenteredLaw_regular
    hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz
  have he (u : ℝ≥0) := finiteCenteredLaw_congr_driver hCB κ γ G z u
  refine ⟨C, fun t => hCm.comp (measurable_const.prodMk measurable_id), ρ, hρ, hCB, hρeq, ?_, ?_⟩
  · intro u
    rw [← he u]
    exact hprob u
  · intro u v huv A hA
    rw [← he u, ← he v]
    exact hcon u v huv A hA

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def inverseAngleSubcritical (κ : ℝ) : ℝ :=
  greenExponent κ - min (greenExponent κ / 2) 1
noncomputable def inverseAngleBuffer (u₀ : ℝ) : ℝ := min (u₀ / 2) 1
noncomputable def uniformInverseAngleConstant (κ u₀ : ℝ) : ℝ :=
  inverseAngleBound κ (inverseAngleSubcritical κ) (inverseAngleBuffer u₀)

lemma inverseAngleSubcritical_bounds (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < inverseAngleSubcritical κ ∧ inverseAngleSubcritical κ < greenExponent κ ∧
      greenExponent κ ≤ inverseAngleSubcritical κ + 2 := by
  have ha := greenExponent_pos κ hκ hκ8
  unfold inverseAngleSubcritical
  have hm0 : 0 < min (greenExponent κ / 2) 1 := lt_min (by positivity) (by norm_num)
  have hm := min_le_left (greenExponent κ / 2) 1
  have hm1 := min_le_right (greenExponent κ / 2) 1
  constructor
  · linarith
  constructor <;> linarith

lemma uniformInverseAngleConstant_pos (κ u₀ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (hu₀ : 0 < u₀) :
    0 < uniformInverseAngleConstant κ u₀ := by
  have hb := inverseAngleSubcritical_bounds κ hκ hκ8
  exact inverseAngleBound_pos hκ hb.1 hb.2.1 (lt_min (by positivity) (by norm_num))

 

theorem uniform_inverse_angle_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u₀ : ℝ) (hu₀ : 0 < u₀)
    (v : ℝ≥0) (hv : u₀ ≤ v) :
    Integrable (fun ω => stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ))
      (finiteCenteredLaw P κ B γ G z v) ∧
    (∫ ω, stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ)
      ∂finiteCenteredLaw P κ B γ G z v) ≤ uniformInverseAngleConstant κ u₀ := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (u : ℝ≥0) (n : ℕ) : AngularLocalization B hm κ z u (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z u (ε n)
      u.coe_nonneg (hε0 n) (hεA n))
  obtain ⟨hi, he⟩ := finiteCenteredLaw_inverseAngle_moment hB hBm hBc κ hκ hκ8 γ G F hw z hz v v.coe_nonneg
    (a v) hεanti hεlim (greenExponent κ) le_rfl
  refine ⟨hi, he.trans_le ?_⟩
  have hb := inverseAngleSubcritical_bounds κ hκ hκ8
  apply radiusMoment_inverseAngle_bound a hεanti hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz
    (inverseAngleSubcritical κ) hb.1 hb.2.1 hb.2.2
    (inverseAngleBuffer u₀) (lt_min (by positivity) (by norm_num)) (min_le_right _ _)
  have hη := min_le_left (u₀ / 2) 1
  dsimp only [inverseAngleBuffer]
  linarith

 

theorem uniform_inverse_angle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u₀ : ℝ) (hu₀ : 0 < u₀)
    (v : ℝ≥0) (hv : u₀ ≤ v) :
    Integrable (fun ω => stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ))
      (finiteCenteredLaw P κ B γ G z v) ∧
    (∫ ω, stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ)
      ∂finiteCenteredLaw P κ B γ G z v) ≤ uniformInverseAngleConstant κ u₀ := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω he
    simpa only [he] using hω
  obtain ⟨hi, hb⟩ := uniform_inverse_angle_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz u₀ hu₀ v hv
  rw [finiteCenteredLaw_congr_driver hCB κ γ G z v] at hi hb
  have he : (fun ω => stoppedInverseAngle κ (fun t => C t ω) (γ ω) (G ω) z v (greenExponent κ)) =ᵐ[finiteCenteredLaw P κ B γ G z v]
      (fun ω => stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z v (greenExponent κ)) := by
    have hCB' : ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G z v, ∀ t, C t ω = B t ω :=
      (withDensity_absolutelyContinuous P _).ae_le hCB
    filter_upwards [hCB'] with ω he
    simp only [stoppedInverseAngle, stoppedAngleSq, he]
  exact ⟨hi.congr he, (integral_congr_ae he).symm.trans_le hb⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma radius_approach_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) :
    (P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞}).toReal ≤
      uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  let hm (t) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let A₀ := logAngleSq κ (initialLogCoordinates z) 0
  have hA₀ : 0 < A₀ := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A₀ / ((n : ℝ) + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A₀ := div_le_self hA₀.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A₀
    simpa only [mul_one_div, mul_zero] using hh
  have hεanti : Antitone ε := by
    intro n m hnm
    exact div_le_div_of_nonneg_left hA₀.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  let a (n : ℕ) : AngularLocalization B hm κ z v (ε n) :=
    Classical.choice (exists_angularLocalization hB hm hBm hBc hB0 κ hκ hκ8 z v (ε n)
      v.coe_nonneg (hε0 n) (hεA n))
  have hbound := (uniform_inverse_angle_regular hB hBm hBc hB0 κ hκ hκ8 γ G F hw z hz
    1 (by norm_num) v hv).2
  have he := (finiteCenteredLaw_inverseAngle_moment hB hBm hBc κ hκ hκ8 γ G F hw z hz v v.coe_nonneg
    a hεanti hεlim (greenExponent κ) le_rfl).2
  rw [he, radiusMoment, sub_self,
    integral_limitRadiusKernel_zero_eq_probability a hεanti hεlim hBm hBc hz v.coe_nonneg γ G F hw] at hbound
  have hmult := (div_le_iff₀ (initialGreen_pos κ z hz)).mp hbound
  calc
    (P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞}).toReal ≤
        uniformInverseAngleConstant κ 1 * initialGreen κ z /
          Real.exp (codimension κ * ((v : ℝ) - Real.log 2 - Real.log z.im)) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [mul_comm] using hmult
    _ = uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
      rw [mul_div_assoc, initialGreen_div_zeroKernel κ v z hz, mul_assoc]

 

theorem radius_approach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) :
    (P {ω | radiusLevelTime (γ ω) (G ω) z v < ∞}).toReal ≤
      uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω he
    simpa only [he] using hω
  exact radius_approach_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz v hv

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem euclidean_approach_at_level
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ))
    (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (hscale : (128 * Real.pi) * r ≤ (2 * z.im) * Real.exp (-v)) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * v) *
        (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  apply le_trans _ (radius_approach hB κ hκ hκ8 γ G F hw z hz v hv)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hw, hB.cont] with ω hω hc
  rintro ⟨t, ht⟩
  have hU : Continuous (fun s => Real.sqrt κ * B s ω) := hc.const_mul _
  obtain ⟨s, _, hsl, hsR⟩ := hω.radius_approach_of_trace_approach hU z r hr hy t ht
  exact radiusLevelTime_finite_of_live_radius_lt hU hω z v v.coe_nonneg s hsl
    (hsR.trans_le hscale)

 

theorem euclidean_approach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (r : ℝ) (hr : 0 < r)
    (hy : r ≤ z.im)
    (hsmall : 1 ≤ Real.log ((2 * z.im) / ((128 * Real.pi) * r))) :
    (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
      (uniformInverseAngleConstant κ 1 * (128 * Real.pi) ^ codimension κ) *
        initialGreen κ z * r ^ codimension κ := by
  let u := Real.log ((2 * z.im) / ((128 * Real.pi) * r))
  have hu : 0 ≤ u := (by norm_num : (0 : ℝ) ≤ 1).trans hsmall
  have hC : 0 < 128 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hy0 : 0 < 2 * z.im := mul_pos (by norm_num) hz
  have hratio : 0 < (2 * z.im) / ((128 * Real.pi) * r) := div_pos hy0 (mul_pos hC hr)
  have he : (2 * z.im) * Real.exp (-u) = (128 * Real.pi) * r := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
  have hb := euclidean_approach_at_level hB κ hκ hκ8 γ G F hw z hz
    ⟨u, hu⟩ hsmall r hr hy he.ge
  have hexp : Real.exp (-codimension κ * u) =
      (128 * Real.pi) ^ codimension κ * r ^ codimension κ *
        (2 * z.im) ^ (-codimension κ) := by
    rw [Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hr,
      Real.rpow_def_of_pos hy0, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [u]
    rw [Real.log_div hy0.ne' (mul_pos hC hr).ne', Real.log_mul hC.ne' hr.ne']
    ring
  change (P {ω | ∃ t : ℝ≥0, dist (γ ω t) z < r}).toReal ≤
    uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * u) *
      (Real.sin (Complex.arg z)) ^ greenExponent κ at hb
  rw [hexp] at hb
  simpa only [initialGreen, mul_assoc, mul_comm, mul_left_comm] using hb

end SLEExactGauge
end

 
end

end OAI
