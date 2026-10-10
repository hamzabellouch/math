import Mathlib
import OAI.Geometry.WeakHessian.Transport.CouplingCostBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def midpointSigmaLower (K N D : ℝ) : ℝ :=
  1 / (2 * Real.exp (D * Real.sqrt (|K| / N)))

lemma midpointSigmaLower_pos (K N D : ℝ) : 0 < midpointSigmaLower K N D := by
  dsimp [midpointSigmaLower]
  positivity

lemma midpointSigmaLower_le_half (K N : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    midpointSigmaLower K N D ≤ 1 / 2 := by
  have he := Real.one_le_exp_iff.mpr (mul_nonneg hD (Real.sqrt_nonneg (|K| / N)))
  dsimp [midpointSigmaLower]
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

lemma midpoint_sin_ratio {x : ℝ} (hx : 0 < x) (hpi : x < Real.pi) :
    (1 : ℝ)/2 ≤ Real.sin (x/2) / Real.sin x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hpi
  have hh := Real.sin_pos_of_pos_of_lt_pi (show 0 < x/2 by linarith)
    (show x/2 < Real.pi by linarith [Real.pi_pos])
  rw [le_div_iff₀ hs]
  have hid : Real.sin x = 2*Real.sin (x/2)*Real.cos (x/2) := by
    have hh := Real.sin_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at hh
    exact hh
  nlinarith [Real.cos_le_one (x/2)]

lemma midpoint_sinh_ratio {x A : ℝ} (hx : 0 < x) (hA : x/2 ≤ A) (_hA0 : 0 ≤ A) :
    1 / (2*Real.exp A) ≤ Real.sinh (x/2) / Real.sinh x := by
  have hs := Real.sinh_pos_iff.mpr hx
  have hh := Real.sinh_pos_iff.mpr (show 0 < x/2 by linarith)
  have hc : Real.cosh (x/2) ≤ Real.exp A := by
    rw [Real.cosh_eq]
    have he₁ := Real.exp_le_exp.mpr hA
    have he₂ := Real.exp_le_exp.mpr (show -(x/2) ≤ A by linarith)
    linarith
  have hid : Real.sinh x = 2*Real.sinh (x/2)*Real.cosh (x/2) := by
    have hh := Real.sinh_two_mul (x/2)
    rw [show 2*(x/2)=x by ring] at hh
    exact hh
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith

lemma sigmaCoeff_midpoint_lower {K N D θ : ℝ} (hN : 0 < N)
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθD : θ ≤ D) :
    ENNReal.ofReal (midpointSigmaLower K N D) ≤ sigmaCoeff K N (1/2) θ := by
  have hc := midpointSigmaLower_le_half K N hD
  unfold sigmaCoeff
  simp only [show ¬(1/2 : ℝ) ≤ 0 by norm_num, show ¬1 ≤ (1/2 : ℝ) by norm_num,
    ite_false]
  split_ifs with hzero hK hcut hKzero
  · exact ENNReal.ofReal_le_ofReal hc
  · apply ENNReal.ofReal_le_ofReal
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (K/N) := Real.sqrt_pos.mpr (div_pos hK hN)
    have hx : 0 < θ * Real.sqrt (K/N) := mul_pos hθpos hroot
    have hsq : (θ * Real.sqrt (K/N))^2 * N = K*θ^2 := by
      rw [mul_pow, Real.sq_sqrt (div_pos hK hN).le]
      field_simp
    have hslt : (θ * Real.sqrt (K/N))^2 < Real.pi^2 := by
      apply (mul_lt_mul_iff_left₀ hN).mp
      rw [hsq]
      nlinarith [hcut]
    have hpi : θ * Real.sqrt (K/N) < Real.pi := by
      nlinarith [Real.pi_pos]
    have hh := midpoint_sin_ratio hx hpi
    have he : (1/2 : ℝ)*θ*Real.sqrt (K/N) = (θ*Real.sqrt (K/N))/2 := by ring
    rw [he]
    exact hc.trans hh
  · exact le_top
  · exact ENNReal.ofReal_le_ofReal hc
  · apply ENNReal.ofReal_le_ofReal
    have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hK) hKzero
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    have hroot : 0 < Real.sqrt (-K/N) := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) hN)
    have hx : 0 < θ * Real.sqrt (-K/N) := mul_pos hθpos hroot
    have hA : (θ*Real.sqrt (-K/N))/2 ≤ D*Real.sqrt (-K/N) := by
      nlinarith
    have hh := midpoint_sinh_ratio hx hA (mul_nonneg hD hroot.le)
    have he : (1/2 : ℝ)*θ*Real.sqrt (-K/N) = (θ*Real.sqrt (-K/N))/2 := by ring
    rw [he]
    simpa only [midpointSigmaLower, abs_of_neg hKneg] using hh

def midpointTauLower (K N D : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/2 : ℝ) ^ (1/N) *
    ENNReal.ofReal (midpointSigmaLower K (N-1) D) ^ ((N-1)/N)

lemma midpointTauLower_pos (K N D : ℝ) : 0 < midpointTauLower K N D := by
  apply ENNReal.mul_pos_iff.mpr
  constructor
  · exact ENNReal.rpow_pos (by norm_num) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (midpointSigmaLower_pos _ _ _))
      ENNReal.ofReal_ne_top

lemma midpointTauLower_ne_top {K N D : ℝ} (hN : 1 < N) :
    midpointTauLower K N D ≠ ∞ := by
  unfold midpointTauLower
  apply ENNReal.mul_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  · exact ENNReal.rpow_ne_top_of_nonneg (div_nonneg (by linarith) (by linarith))
      ENNReal.ofReal_ne_top

lemma tauCoeff_midpoint_lower {K N D θ : ℝ} (hN : 1 < N)
    (hD : 0 ≤ D) (hθ : 0 ≤ θ) (hθD : θ ≤ D) :
    midpointTauLower K N D ≤ tauCoeff K N (1/2) θ := by
  unfold midpointTauLower tauCoeff
  apply mul_le_mul_right
  exact ENNReal.rpow_le_rpow (sigmaCoeff_midpoint_lower (by linarith) hD hθ hθD)
    (div_nonneg (by linarith) (by linarith))

omit [MetricSpace X] [BorelSpace X] in

lemma renyiIntegral_le_support {m μ : Measure X} [IsProbabilityMeasure μ]
    {Q : Set X} (hQ : MeasurableSet Q) (hμ : μ Qᶜ = 0) {N : ℝ} (hN : 1 < N) :
    renyiIntegral m μ N ≤ (m Q) ^ (1/N) := by
  have hNpos : 0 < N := by linarith
  have hNm : 0 < N-1 := by linarith
  have hp : 0 < 1-1/N := by rw [sub_pos, div_lt_one hNpos]; exact hN
  have hconj : (N/(N-1)).HolderConjugate N := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hNm]; linarith
    · field_simp; ring
  have hrn : Measurable (μ.rnDeriv m) := Measure.measurable_rnDeriv μ m
  have hz : μ.rnDeriv m =ᵐ[m.restrict Qᶜ] 0 := by
    apply (lintegral_eq_zero_iff hrn).mp
    exact le_antisymm ((Measure.setLIntegral_rnDeriv_le Qᶜ).trans_eq hμ) bot_le
  have hzpow : (∫⁻ x in Qᶜ, (μ.rnDeriv m x)^(1-1/N) ∂m) = 0 := by
    apply (lintegral_eq_zero_iff (hrn.pow_const _)).mpr
    filter_upwards [hz] with x hx
    simp only [hx, Pi.zero_apply, ENNReal.zero_rpow_of_pos hp]
  have hsplit : renyiIntegral m μ N = ∫⁻ x in Q, (μ.rnDeriv m x)^(1-1/N) ∂m := by
    rw [renyiIntegral, ← lintegral_add_compl _ hQ, hzpow, add_zero]
  rw [hsplit]
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (m.restrict Q) hconj
    ((hrn.pow_const (1-1/N)).aemeasurable) (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  have he₁ : (1-1/N)*(N/(N-1)) = 1 := by field_simp
  have he₂ : 1/(N/(N-1)) = 1-1/N := by field_simp
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul, ← ENNReal.rpow_mul, he₁, ENNReal.rpow_one, he₂] at hh
  refine hh.trans ?_
  have hm : (∫⁻ x in Q, μ.rnDeriv m x ∂m) ≤ 1 :=
    (Measure.setLIntegral_rnDeriv_le Q).trans ((measure_mono (subset_univ Q)).trans_eq (measure_univ))
  calc
    (∫⁻ x in Q, μ.rnDeriv m x ∂m) ^ (1-1/N) * (m Q) ^ (1/N) ≤
        1 ^ (1-1/N) * (m Q) ^ (1/N) :=
      mul_le_mul_left (ENNReal.rpow_le_rpow hm hp.le) _
    _ = (m Q) ^ (1/N) := by simp

def normalizedRestriction (m : Measure X) (Q : Set X) : Measure X :=
  (m Q)⁻¹ • m.restrict Q

omit [MetricSpace X] [BorelSpace X] in
lemma normalizedRestriction_ac (m : Measure X) (Q : Set X) :
    normalizedRestriction m Q ≪ m :=
  Measure.absolutelyContinuous_restrict.smul_left _

omit [MetricSpace X] [BorelSpace X] in
lemma normalizedRestriction_ae_mem (m : Measure X) {Q : Set X} (hQ : MeasurableSet Q) :
    ∀ᵐ x ∂normalizedRestriction m Q, x ∈ Q :=
  (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le (ae_restrict_mem hQ)

omit [MetricSpace X] [BorelSpace X] in
lemma normalizedRestriction_probability (m : Measure X) {Q : Set X}
    (h₀ : m Q ≠ 0) (htop : m Q ≠ ∞) : IsProbabilityMeasure (normalizedRestriction m Q) := by
  refine ⟨?_⟩
  simp only [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h₀ htop

lemma interpolation_probability (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (t : Time) : IsProbabilityMeasure (interpolation π t) :=
  (Measure.isProbabilityMeasure_map_iff
    (continuous_eval_const t).measurable.aemeasurable).mpr inferInstance

omit [BorelSpace X] in
lemma sigmaFinite_of_finiteOnBoundedSets (m : Measure X) (h : FiniteOnBoundedSets m)
    (o : X) : SigmaFinite m := by
  refine ⟨⟨⟨(fun n : ℕ => Metric.ball o (n : ℝ)), (fun _ => trivial),
    (fun n => h _ (Metric.isBounded_ball)), ?_⟩⟩⟩
  ext x
  simp only [mem_iUnion, Metric.mem_ball, mem_univ, iff_true]
  exact exists_nat_gt (dist x o)

omit [MetricSpace X] [BorelSpace X] in
lemma rnDeriv_normalizedRestriction {m : Measure X} [SigmaFinite m] {Q : Set X}
    (hQ : MeasurableSet Q) (h₀ : m Q ≠ 0) :
    (normalizedRestriction m Q).rnDeriv m =ᵐ[normalizedRestriction m Q] fun _ => (m Q)⁻¹ := by
  have hs := Measure.rnDeriv_smul_left_of_ne_top' (m.restrict Q) m
    (ENNReal.inv_ne_top.mpr h₀)
  have hr := Measure.rnDeriv_restrict_self m hQ
  filter_upwards [(normalizedRestriction_ac m Q).ae_le hs,
    (normalizedRestriction_ac m Q).ae_le hr, normalizedRestriction_ae_mem m hQ] with x hx hy hmem
  change (normalizedRestriction m Q).rnDeriv m x = (m Q)⁻¹ * (m.restrict Q).rnDeriv m x at hx
  rw [hx, hy, indicator_of_mem hmem, Pi.one_apply, mul_one]

omit [BorelSpace X] in
lemma hasSecondMoment_of_ae_dist_le {μ : Measure X} [IsProbabilityMeasure μ]
    (o : X) (R : ℝ) (h : ∀ᵐ x ∂μ, dist x o ≤ R) : HasSecondMoment μ := by
  refine ⟨o, ?_⟩
  calc
    (∫⁻ x, (edist x o)^2 ∂μ) ≤ ∫⁻ x, (ENNReal.ofReal R)^2 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [h] with x hx
      rw [edist_dist]
      exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hx) 2
    _ < ∞ := by simp

lemma cd_midpoint_ball_volume {m : Measure X} {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {R D : ℝ}
    (hR : 0 < R) (hD : 2*R ≤ D) :
    midpointTauLower K N D * (m (Metric.ball o R))^(1/N) ≤
      (m (Metric.ball o (3*R/4)))^(1/N) := by
  let : SigmaFinite m := sigmaFinite_of_finiteOnBoundedSets m hfin o
  let A := Metric.ball o (R/12)
  let B := Metric.ball o R
  let Q := Metric.ball o (3*R/4)
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hQ : MeasurableSet Q := Metric.isOpen_ball.measurableSet
  have hApos : 0 < m A := hfull A Metric.isOpen_ball ⟨o, Metric.mem_ball_self (by positivity)⟩
  have hBpos : 0 < m B := hfull B Metric.isOpen_ball ⟨o, Metric.mem_ball_self hR⟩
  have hAfin : m A ≠ ∞ := (hfin A Metric.isBounded_ball).ne
  have hBfin : m B ≠ ∞ := (hfin B Metric.isBounded_ball).ne
  let μ₀ := normalizedRestriction m A
  let μ₁ := normalizedRestriction m B
  let : IsProbabilityMeasure μ₀ := normalizedRestriction_probability m hApos.ne' hAfin
  let : IsProbabilityMeasure μ₁ := normalizedRestriction_probability m hBpos.ne' hBfin
  have hmem₀ : ∀ᵐ x ∂μ₀, x ∈ A := normalizedRestriction_ae_mem m hA
  have hmem₁ : ∀ᵐ x ∂μ₁, x ∈ B := normalizedRestriction_ae_mem m hB
  have hmom₀ : HasSecondMoment μ₀ := hasSecondMoment_of_ae_dist_le o (R/12)
    (hmem₀.mono (fun _ hx => hx.le))
  have hmom₁ : HasSecondMoment μ₁ := hasSecondMoment_of_ae_dist_le o R
    (hmem₁.mono (fun _ hx => hx.le))
  obtain ⟨π, hπ, hgeo, hopt, hrenyi⟩ := hCD μ₀ μ₁ inferInstance inferInstance
    hmom₀ hmom₁ (normalizedRestriction_ac m A) (normalizedRestriction_ac m B)
  let := hπ
  let t : Time := ⟨1/2, by norm_num, by norm_num⟩
  have hends := hopt.1.interpolation_endpoints
  have he₀ : ∀ᵐ γ ∂π, γ timeZero ∈ A := by
    apply ae_of_ae_map (continuous_eval_const timeZero).measurable.aemeasurable
    simpa only [← hends.1, interpolation] using hmem₀
  have he₁ : ∀ᵐ γ ∂π, γ timeOne ∈ B := by
    apply ae_of_ae_map (continuous_eval_const timeOne).measurable.aemeasurable
    simpa only [← hends.2, interpolation] using hmem₁
  have hdens : ∀ᵐ γ ∂π, μ₁.rnDeriv m (γ timeOne) = (m B)⁻¹ := by
    apply ae_of_ae_map (p := fun x => μ₁.rnDeriv m x = (m B)⁻¹)
      (continuous_eval_const timeOne).measurable.aemeasurable
    change ∀ᵐ y ∂interpolation π timeOne, μ₁.rnDeriv m y = (m B)⁻¹
    rw [hends.2]
    exact rnDeriv_normalizedRestriction hB hBpos.ne'
  have hlength : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D := by
    filter_upwards [he₀, he₁] with γ h₀ h₁
    have hd := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o] at hd
    change dist (γ timeZero) o < R/12 at h₀
    change dist (γ timeOne) o < R at h₁
    linarith
  have hmid : ∀ᵐ γ ∂π, γ t ∈ Q := by
    filter_upwards [hgeo, he₀, he₁] with γ hg h₀ h₁
    have hd := dist_triangle (γ timeZero) o (γ timeOne)
    rw [dist_comm o] at hd
    have hw := dist_triangle (γ t) (γ timeZero) o
    rw [hg t timeZero] at hw
    change dist (γ timeZero) o < R/12 at h₀
    change dist (γ timeOne) o < R at h₁
    change dist (γ t) o < 3*R/4
    change dist (γ t) o ≤ |(1/2 : ℝ)-0| *
      dist (γ timeZero) (γ timeOne) + dist (γ timeZero) o at hw
    norm_num only [sub_zero, abs_of_pos (by norm_num : 0 < (1/2 : ℝ))] at hw
    linarith
  have hmidsupp : (interpolation π t) Qᶜ = 0 := by
    apply ae_iff.mp
    apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable hQ).mpr
    exact hmid
  let := interpolation_probability π t
  have hu : renyiIntegral m (interpolation π t) N ≤ (m Q)^(1/N) :=
    renyiIntegral_le_support hQ hmidsupp hN
  have hl := hrenyi N le_rfl t
  refine le_trans ?_ (hl.trans hu)
  have hid : ((m B)⁻¹)^(-1/N) = (m B)^(1/N) := by
    rw [ENNReal.inv_rpow, show -1/N = -(1/N) by ring, ENNReal.rpow_neg, inv_inv]
  calc
    midpointTauLower K N D * (m B)^(1/N) =
        ∫⁻ _ : Curve X, midpointTauLower K N D * (m B)^(1/N) ∂π := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hlength, hdens] with γ hlen hrho
      refine le_trans ?_ (le_add_left le_rfl)
      rw [hrho, hid]
      exact mul_le_mul_left
        (tauCoeff_midpoint_lower hN (by linarith) dist_nonneg hlen) _

lemma cd_iterated_ball_volume {m : Measure X} {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    (midpointTauLower K N (2*R))^n * (m (Metric.ball o R))^(1/N) ≤
      (m (Metric.ball o ((3/4 : ℝ)^n*R)))^(1/N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : 0 < (3/4 : ℝ)^n * R := mul_pos (pow_pos (by norm_num) _) hR
    have hrle : (3/4 : ℝ)^n * R ≤ R := by
      nlinarith [pow_le_one₀ (n := n) (by norm_num : 0 ≤ (3/4 : ℝ)) (by norm_num)]
    have hs := cd_midpoint_ball_volume hN hCD hfull hfin o hr
      (show 2*((3/4 : ℝ)^n*R) ≤ 2*R by linarith)
    calc
      (midpointTauLower K N (2*R))^(n+1) * (m (Metric.ball o R))^(1/N) =
          midpointTauLower K N (2*R) *
            ((midpointTauLower K N (2*R))^n * (m (Metric.ball o R))^(1/N)) := by
        rw [pow_succ]; ac_rfl
      _ ≤ midpointTauLower K N (2*R) *
          (m (Metric.ball o ((3/4 : ℝ)^n*R)))^(1/N) := mul_le_mul_right ih _
      _ ≤ (m (Metric.ball o ((3/4 : ℝ)^(n+1)*R)))^(1/N) := by
        have he : 3*((3/4 : ℝ)^n*R)/4 = (3/4 : ℝ)^(n+1)*R := by
          rw [pow_succ]; ring
        simpa only [he] using hs

lemma cd_uniform_ball_measure_lower {m : Measure X} {K N : ℝ} (hN : 1 < N)
    (hCD : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ δ ≠ ∞ ∧
      ∀ x ∈ Metric.closedBall o R, δ ≤ m (Metric.ball x r) := by
  let S := 2*R+2
  have hS : 0 < S := by dsimp [S]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hr hS) (by norm_num : (3/4 : ℝ) < 1)
  have hn' : (3/4 : ℝ)^n*S < r := (lt_div_iff₀ hS).mp hn
  let p : ℝ≥0∞ := (midpointTauLower K N (2*S))^n * (m (Metric.ball o 1))^(1/N)
  have hbase : 0 < m (Metric.ball o 1) :=
    hfull _ Metric.isOpen_ball ⟨o, Metric.mem_ball_self zero_lt_one⟩
  have hbasefin : m (Metric.ball o 1) ≠ ∞ := (hfin _ Metric.isBounded_ball).ne
  have hp : 0 < p := ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.pow_pos (midpointTauLower_pos _ _ _) _, ENNReal.rpow_pos hbase hbasefin⟩
  have hpfin : p ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (midpointTauLower_ne_top hN))
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hbasefin)
  refine ⟨p^N, ENNReal.rpow_pos hp hpfin,
    ENNReal.rpow_ne_top_of_nonneg (by linarith) hpfin, ?_⟩
  intro x hx
  have hsub : Metric.ball o 1 ⊆ Metric.ball x S := by
    apply Metric.ball_subset_ball'
    have hx' : dist x o ≤ R := hx
    rw [dist_comm o]
    dsimp [S]
    linarith
  have hlow : p ≤ (m (Metric.ball x r))^(1/N) := by
    calc
      p ≤ (midpointTauLower K N (2*S))^n * (m (Metric.ball x S))^(1/N) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow (measure_mono hsub) (by positivity)) _
      _ ≤ (m (Metric.ball x ((3/4 : ℝ)^n*S)))^(1/N) :=
        cd_iterated_ball_volume hN hCD hfull hfin x hS n
      _ ≤ (m (Metric.ball x r))^(1/N) :=
        ENNReal.rpow_le_rpow (measure_mono (Metric.ball_subset_ball hn'.le)) (by positivity)
  have hh := ENNReal.rpow_le_rpow hlow (show 0 ≤ N by linarith)
  rwa [← ENNReal.rpow_mul, div_mul_cancel₀ 1 (show N ≠ 0 by linarith), ENNReal.rpow_one] at hh

lemma properSpace_of_cd [CompleteSpace X] [SecondCountableTopology X]
    {m : Measure X} {K N : ℝ} (hN : 1 < N) (hCD : CurvatureDimension m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) : ProperSpace X := by
  constructor
  intro o R
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_, Metric.isClosed_closedBall.isComplete⟩
  apply Metric.totallyBounded_iff.mpr
  intro r hr
  obtain ⟨δ, hδ, _, hvol⟩ := cd_uniform_ball_measure_lower hN hCD hfull hfin o
    (le_max_right R 0) (half_pos hr)
  let U := Metric.ball o (max R 0+r+1)
  let ν := m.restrict U
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (hfin U Metric.isBounded_ball).ne
  obtain ⟨S, hS, hsmall⟩ := exists_isCompact_closure_measure_compl_lt ν δ hδ
  have hsmall' : ν (closure S)ᶜ < δ :=
    (measure_mono (compl_subset_compl.mpr subset_closure)).trans_lt hsmall
  obtain ⟨T, hTfin, hcover⟩ := Metric.totallyBounded_iff.mp hS.totallyBounded (r/2) (half_pos hr)
  refine ⟨T, hTfin, ?_⟩
  intro x hx
  have hx' : dist x o ≤ max R 0 := (show dist x o ≤ R from hx).trans (le_max_left _ _)
  have hU : Metric.ball x (r/2) ⊆ U := by
    apply Metric.ball_subset_ball'
    linarith
  have hν : δ ≤ ν (Metric.ball x (r/2)) := by
    change δ ≤ (m.restrict U) (Metric.ball x (r/2))
    rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_eq_left.mpr hU]
    exact hvol x hx'
  have hinter : (Metric.ball x (r/2) ∩ closure S).Nonempty := by
    by_contra hempty
    have hsub : Metric.ball x (r/2) ⊆ (closure S)ᶜ := by
      intro y hy hys
      exact hempty ⟨y, hy, hys⟩
    exact (not_le_of_gt hsmall') (hν.trans (measure_mono hsub))
  obtain ⟨y, hyball, hyS⟩ := hinter
  obtain ⟨z, hzT, hyz⟩ := mem_iUnion₂.mp (hcover hyS)
  apply mem_iUnion₂.mpr
  refine ⟨z, hzT, ?_⟩
  have hxy : dist x y < r/2 := by simpa only [Metric.mem_ball, dist_comm] using hyball
  have hyz' : dist y z < r/2 := hyz
  exact (dist_triangle x y z).trans_lt (by linarith)

end WeakHessian

end
end InlinedFile0

end OAI
