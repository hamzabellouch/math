import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
namespace RPISingularHarnack
namespace SphericalFrankel

abbrev Frame (n : ℕ) := Euc n × Euc n

def IsFrame {n : ℕ} (e : Frame n) : Prop :=
  ‖e.1‖ = 1 ∧ ‖e.2‖ = 1 ∧ inner ℝ e.1 e.2 = 0

def proj {n : ℕ} (e : Frame n) (v : Euc n) : Euc n :=
  v - (inner ℝ e.1 v) • e.1 - (inner ℝ e.2 v) • e.2

def angle {n : ℕ} (e f : Frame n) : ℝ := inner ℝ e.1 f.1

def defect {n : ℕ} (e f : Frame n) : ℝ := ‖proj e f.1‖ ^ 2

def traceProduct {n : ℕ} (e f : Frame n) : ℝ :=
  (n : ℝ) - 4 + angle e f ^ 2 + (inner ℝ e.1 f.2) ^ 2 +
    (inner ℝ e.2 f.1) ^ 2 + (inner ℝ e.2 f.2) ^ 2

def cross {n : ℕ} (e f : Frame n) : ℝ := inner ℝ (proj e f.1) (proj f e.1)

lemma proj_inner_self {n : ℕ} {e : Frame n} (he : IsFrame e) (v : Euc n) :
    inner ℝ (proj e v) (proj e v) =
      ‖v‖ ^ 2 - (inner ℝ e.1 v) ^ 2 - (inner ℝ e.2 v) ^ 2 := by
  have h11 : inner ℝ e.1 e.1 = 1 := by simp [he.1]
  have h22 : inner ℝ e.2 e.2 = 1 := by simp [he.2.1]
  have h21 : inner ℝ e.2 e.1 = 0 := by rw [real_inner_comm, he.2.2]
  simp only [proj, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, h11, h22, he.2.2, h21, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v e.1, real_inner_comm v e.2]
  ring

lemma defect_eq {n : ℕ} {e f : Frame n} (he : IsFrame e) (hf : IsFrame f) :
    defect e f = 1 - angle e f ^ 2 - (inner ℝ e.2 f.1) ^ 2 := by
  rw [defect, ← real_inner_self_eq_norm_sq, proj_inner_self he, hf.1]
  simp [angle]

lemma cross_eq {n : ℕ} {e f : Frame n} (he : IsFrame e) (hf : IsFrame f) :
    cross e f = angle e f * (-1 + angle e f ^ 2 +
      (inner ℝ e.2 f.1) ^ 2 + (inner ℝ e.1 f.2) ^ 2) +
      (inner ℝ e.2 f.1) * (inner ℝ e.1 f.2) * (inner ℝ e.2 f.2) := by
  have hs : inner ℝ f.1 f.2 = 0 := hf.2.2
  have ht : inner ℝ e.2 e.1 = 0 := by rw [real_inner_comm, he.2.2]
  simp only [cross, proj, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial, hs, ht, real_inner_self_eq_norm_sq, he.1, hf.1]
  dsimp [angle]
  simp only [real_inner_comm f.1 e.1, real_inner_comm f.2 e.1]
  ring

lemma cross_abs_le {n : ℕ} (e f : Frame n) :
    |cross e f| ≤ (defect e f + defect f e) / 2 := by
  have h := abs_real_inner_le_norm (proj e f.1) (proj f e.1)
  dsimp [cross, defect]
  nlinarith [sq_nonneg (‖proj e f.1‖ - ‖proj f e.1‖)]

lemma angle_abs_le_one {n : ℕ} {e f : Frame n} (he : IsFrame e) (hf : IsFrame f) :
    |angle e f| ≤ 1 := by
  simpa [angle, he.1, hf.1] using abs_real_inner_le_norm e.1 f.1

lemma traceProduct_eq {n : ℕ} {e f : Frame n} (he : IsFrame e) (hf : IsFrame f) :
    traceProduct e f = (n : ℝ) - 2 - angle e f ^ 2 +
      (inner ℝ e.2 f.2) ^ 2 - (defect e f + defect f e) := by
  rw [traceProduct, defect_eq he hf, defect_eq hf he]
  rw [real_inner_comm f.2 e.1]
  have h : angle f e = angle e f := real_inner_comm _ _
  rw [h]
  ring

lemma scalar_gap_bound {c f a b d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hf0 : 0 ≤ f) (hfc : f ≤ c)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hd : |d| ≤ 1)
    (hA : 0 ≤ 1 - f ^ 2 - a ^ 2) (hB : 0 ≤ 1 - f ^ 2 - b ^ 2)
    (hcross : |f * (-1 + f ^ 2 + a ^ 2 + b ^ 2) + a * b * d| ≤
      ((1 - f ^ 2 - a ^ 2) + (1 - f ^ 2 - b ^ 2)) / 2) :
    f ^ 2 - d ^ 2 ≤ 3 / (1 - c ^ 2) ^ 2 *
      ((1 - f ^ 2 - a ^ 2) + (1 - f ^ 2 - b ^ 2)) := by
  let s := 1 - f ^ 2
  let U := (1 - f ^ 2 - a ^ 2) + (1 - f ^ 2 - b ^ 2)
  have hf1 : f < 1 := hfc.trans_lt hc1
  have hs : 0 < s := by dsimp [s]; nlinarith
  have hs1 : s ≤ 1 := by dsimp [s]; nlinarith [sq_nonneg f]
  have hU : 0 ≤ U := add_nonneg hA hB
  have ha2 : a ^ 2 ≤ s := by dsimp [s]; linarith
  have hb2 : b ^ 2 ≤ s := by dsimp [s]; linarith
  have hab : a ^ 2 * b ^ 2 ≤ s ^ 2 := by
    simpa [pow_two] using mul_le_mul ha2 hb2 (sq_nonneg b) hs.le
  have habd : |a * b * d| ≤ 1 := by
    rw [abs_mul, abs_mul]
    calc
      |a| * |b| * |d| ≤ 1 * 1 * 1 :=
        mul_le_mul (mul_le_mul ha hb (abs_nonneg b) (by norm_num)) hd
          (abs_nonneg d) (by norm_num)
      _ = 1 := by ring
  have hfs : |f * s| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hf0 hs.le)]
    nlinarith
  have hC : |f * s + a * b * d| ≤ (3 / 2 : ℝ) * U := by
    have hid : f * s + a * b * d =
        (f * (-1 + f ^ 2 + a ^ 2 + b ^ 2) + a * b * d) + f * U := by
      dsimp [s, U]; ring
    rw [hid]
    calc
      _ ≤ |f * (-1 + f ^ 2 + a ^ 2 + b ^ 2) + a * b * d| + |f * U| := abs_add_le _ _
      _ ≤ U / 2 + f * U := by
        rw [abs_of_nonneg (mul_nonneg hf0 hU)]
        change _ ≤ ((1 - f ^ 2 - a ^ 2) + (1 - f ^ 2 - b ^ 2)) / 2 + f * U
        linarith
      _ ≤ (3 / 2 : ℝ) * U := by nlinarith
  have hD : |f * s - a * b * d| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  have hprod : |(f * s) ^ 2 - (a * b * d) ^ 2| ≤ 3 * U := by
    have hid : (f * s) ^ 2 - (a * b * d) ^ 2 =
        (f * s + a * b * d) * (f * s - a * b * d) := by ring
    rw [hid, abs_mul]
    calc
      _ ≤ ((3 / 2 : ℝ) * U) * 2 :=
        mul_le_mul hC hD (abs_nonneg _) (by positivity)
      _ = 3 * U := by ring
  have hgap : (f ^ 2 - d ^ 2) * s ^ 2 ≤ 3 * U := by
    have hmul := mul_le_mul_of_nonneg_right hab (sq_nonneg d)
    have hsq := (le_abs_self ((f * s) ^ 2 - (a * b * d) ^ 2)).trans hprod
    nlinarith only [hmul, hsq]
  have hε : 0 < 1 - c ^ 2 := by nlinarith
  have hεs : 1 - c ^ 2 ≤ s := by dsimp [s]; nlinarith
  have hε2 : (1 - c ^ 2) ^ 2 ≤ s ^ 2 := by nlinarith
  have hεp : 0 < (1 - c ^ 2) ^ 2 := sq_pos_of_pos hε
  change f ^ 2 - d ^ 2 ≤ 3 / (1 - c ^ 2) ^ 2 * U
  rw [div_mul_eq_mul_div, le_div_iff₀ hεp]
  by_cases hsign : 0 ≤ f ^ 2 - d ^ 2
  · exact (mul_le_mul_of_nonneg_left hε2 hsign).trans hgap
  · have hg : f ^ 2 - d ^ 2 ≤ 0 := le_of_lt (lt_of_not_ge hsign)
    exact (mul_nonpos_of_nonpos_of_nonneg hg hεp.le).trans (by positivity)

lemma traceProduct_lower_bound {n : ℕ} {e f : Frame n}
    (he : IsFrame e) (hf : IsFrame f) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hangle0 : 0 ≤ angle e f) (hanglec : angle e f ≤ c) :
    (n : ℝ) - 2 - (1 + 3 / (1 - c ^ 2) ^ 2) * (defect e f + defect f e) ≤
      traceProduct e f := by
  have ha : |inner ℝ e.2 f.1| ≤ 1 := by
    simpa [he.2.1, hf.1] using abs_real_inner_le_norm e.2 f.1
  have hb : |inner ℝ e.1 f.2| ≤ 1 := by
    simpa [he.1, hf.2.1] using abs_real_inner_le_norm e.1 f.2
  have hd : |inner ℝ e.2 f.2| ≤ 1 := by
    simpa [he.2.1, hf.2.1] using abs_real_inner_le_norm e.2 f.2
  have hB : defect f e = 1 - angle e f ^ 2 - (inner ℝ e.1 f.2) ^ 2 := by
    rw [defect_eq hf he, show angle f e = angle e f from real_inner_comm _ _,
      real_inner_comm f.2 e.1]
  have hg := scalar_gap_bound hc0 hc1 hangle0 hanglec ha hb hd
    (show 0 ≤ 1 - angle e f ^ 2 - (inner ℝ e.2 f.1) ^ 2 by
      rw [← defect_eq he hf]; exact sq_nonneg _)
    (show 0 ≤ 1 - angle e f ^ 2 - (inner ℝ e.1 f.2) ^ 2 by
      rw [← hB]; exact sq_nonneg _)
    (show |angle e f * (-1 + angle e f ^ 2 + (inner ℝ e.2 f.1) ^ 2 +
        (inner ℝ e.1 f.2) ^ 2) + (inner ℝ e.2 f.1) * (inner ℝ e.1 f.2) *
        (inner ℝ e.2 f.2)| ≤ _ by
      rw [← cross_eq he hf, ← defect_eq he hf, ← hB]
      exact cross_abs_le e f)
  rw [← defect_eq he hf, ← hB] at hg
  rw [traceProduct_eq he hf]
  nlinarith only [hg]

lemma continuous_proj {n : ℕ} : Continuous (fun p : Frame n × Euc n ↦ proj p.1 p.2) := by
  unfold proj
  fun_prop

lemma continuous_angle {n : ℕ} : Continuous (fun p : Frame n × Frame n ↦ angle p.1 p.2) := by
  unfold angle
  fun_prop

lemma continuous_defect {n : ℕ} : Continuous (fun p : Frame n × Frame n ↦ defect p.1 p.2) := by
  unfold defect proj
  fun_prop

lemma continuous_traceProduct {n : ℕ} :
    Continuous (fun p : Frame n × Frame n ↦ traceProduct p.1 p.2) := by
  unfold traceProduct angle
  fun_prop

lemma continuous_cross {n : ℕ} : Continuous (fun p : Frame n × Frame n ↦ cross p.1 p.2) := by
  unfold cross proj
  fun_prop

lemma isClosed_frames (n : ℕ) : IsClosed {e : Frame n | IsFrame e} := by
  have h1 : IsClosed {e : Frame n | ‖e.1‖ = 1} := isClosed_eq (by fun_prop) continuous_const
  have h2 : IsClosed {e : Frame n | ‖e.2‖ = 1} := isClosed_eq (by fun_prop) continuous_const
  have h3 : IsClosed {e : Frame n | inner ℝ e.1 e.2 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

lemma isCompact_frames (n : ℕ) : IsCompact {e : Frame n | IsFrame e} := by
  apply (isCompact_closedBall (0 : Frame n) 1).of_isClosed_subset (isClosed_frames n)
  intro e he
  simp [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, he.1, he.2.1]

lemma integrable_pairFrameFunction {n : ℕ} {μ : Measure (Frame n × Frame n)}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ p ∂μ, IsFrame p.1 ∧ IsFrame p.2)
    {G : Frame n × Frame n → ℝ} (hG : Continuous G) : Integrable G μ := by
  have hK := (isCompact_frames n).prod (isCompact_frames n)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  apply Integrable.of_bound hG.measurable.aestronglyMeasurable C
  filter_upwards [hμ] with p hp
  exact hC p hp

def angularWeight (t s : ℝ) : ℝ := Real.exp (t * s) * expNegInvGlue s

lemma angularWeight_contDiff (t : ℝ) : ContDiff ℝ ∞ (angularWeight t) :=
  ((contDiff_const.mul contDiff_id).exp).mul expNegInvGlue.contDiff

lemma angularWeight_nonneg (t s : ℝ) : 0 ≤ angularWeight t s :=
  mul_nonneg (Real.exp_pos _).le (expNegInvGlue.nonneg _)

lemma angularWeight_pos_iff (t s : ℝ) : 0 < angularWeight t s ↔ 0 < s := by
  rw [angularWeight, mul_pos_iff_of_pos_left (Real.exp_pos _)]
  constructor
  · intro h
    by_contra hh
    rw [expNegInvGlue.zero_of_nonpos (le_of_not_gt hh)] at h
    exact lt_irrefl 0 h
  · exact expNegInvGlue.pos_of_pos

lemma angularWeight_zero_of_nonpos (t : ℝ) {s : ℝ} (hs : s ≤ 0) :
    angularWeight t s = 0 := by simp [angularWeight, expNegInvGlue.zero_of_nonpos hs]

lemma angularWeight_hasDerivAt (t s : ℝ) :
    HasDerivAt (angularWeight t) ((t + s⁻¹ ^ 2) * angularWeight t s) s := by
  have hg : HasDerivAt expNegInvGlue (s⁻¹ ^ 2 * expNegInvGlue s) s := by
    simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 s
  have he := (((hasDerivAt_id s).const_mul t).exp).mul hg
  have hid : (t + s⁻¹ ^ 2) * angularWeight t s =
      Real.exp (t * id s) * (t * 1) * expNegInvGlue s +
        Real.exp (t * id s) * (s⁻¹ ^ 2 * expNegInvGlue s) := by
    dsimp [angularWeight]
    ring
  rw [hid]
  exact he

lemma angularWeight_deriv (t s : ℝ) :
    deriv (angularWeight t) s = (t + s⁻¹ ^ 2) * angularWeight t s :=
  (angularWeight_hasDerivAt t s).deriv

lemma angularWeight_deriv_lower (t s : ℝ) :
    t * angularWeight t s ≤ deriv (angularWeight t) s := by
  rw [angularWeight_deriv]
  nlinarith [sq_nonneg s⁻¹, angularWeight_nonneg t s]

lemma angularWeight_deriv_nonneg {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    0 ≤ deriv (angularWeight t) s :=
  (mul_nonneg ht (angularWeight_nonneg t s)).trans (angularWeight_deriv_lower t s)

structure CoupledStationarity {n : ℕ} (μ : Measure (Frame n × Frame n)) : Prop where
  gradient : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ →
    (∫ p, deriv φ (angle p.1 p.2) * (defect p.1 p.2 + defect p.2 p.1) ∂μ) =
      2 * ((n : ℝ) - 2) * ∫ p, φ (angle p.1 p.2) * angle p.1 p.2 ∂μ
  mixed : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ →
    2 * (∫ p, φ (angle p.1 p.2) * traceProduct p.1 p.2 ∂μ) -
      ((n : ℝ) - 2) * (∫ p, φ (angle p.1 p.2) *
        (defect p.1 p.2 + defect p.2 p.1) ∂μ) +
      2 * (∫ p, deriv φ (angle p.1 p.2) * cross p.1 p.2 ∂μ) = 0

lemma continuous_defect_sum {n : ℕ} :
    Continuous (fun p : Frame n × Frame n ↦ defect p.1 p.2 + defect p.2 p.1) :=
by
  unfold defect proj
  fun_prop

lemma angularWeight_integral_pos {n : ℕ} (hn : 2 < n)
    {μ : Measure (Frame n × Frame n)} [IsFiniteMeasure μ] (hμ0 : μ ≠ 0)
    (hμ : ∀ᵐ p ∂μ, IsFrame p.1 ∧ IsFrame p.2)
    (hS : CoupledStationarity μ) (t : ℝ) :
    0 < ∫ p, angularWeight t (angle p.1 p.2) ∂μ := by
  have hk : 0 < (n : ℝ) - 2 := by
    have hh : (2 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hiA := integrable_pairFrameFunction hμ (continuous_angle (n := n))
  have hiD := integrable_pairFrameFunction hμ (continuous_defect_sum (n := n))
  have hiT := integrable_pairFrameFunction hμ (continuous_traceProduct (n := n))
  have hiW := integrable_pairFrameFunction hμ
    ((angularWeight_contDiff t).continuous.comp continuous_angle)
  have hW : ∀ᵐ p ∂μ, 0 ≤ angularWeight t (angle p.1 p.2) :=
    Filter.Eventually.of_forall fun p ↦ angularWeight_nonneg t _
  by_contra hpos
  have hz : (∫ p, angularWeight t (angle p.1 p.2) ∂μ) = 0 :=
    le_antisymm (le_of_not_gt hpos) (integral_nonneg_of_ae hW)
  have heq := (integral_eq_zero_iff_of_nonneg_ae hW hiW).mp hz
  have hAnonpos : ∀ᵐ p ∂μ, angle p.1 p.2 ≤ 0 := by
    filter_upwards [heq] with p hp
    by_contra hh
    have h := (angularWeight_pos_iff t _).mpr (lt_of_not_ge hh)
    simp [hp] at h
  have hA : (∫ p, angle p.1 p.2 ∂μ) = 0 := by
    have h := hS.gradient (fun _ ↦ 1) contDiff_const
    simp only [deriv_const, zero_mul, integral_zero, one_mul] at h
    nlinarith
  have hAzero : ∀ᵐ p ∂μ, angle p.1 p.2 = 0 := by
    have hh : (∫ p, -(angle p.1 p.2) ∂μ) = 0 := by rw [integral_neg, hA, neg_zero]
    have he := (integral_eq_zero_iff_of_nonneg_ae
      (hAnonpos.mono (fun p hp ↦ neg_nonneg.mpr hp)) hiA.neg).mp hh
    filter_upwards [he] with p hp
    exact neg_eq_zero.mp hp
  have hD : (∫ p, defect p.1 p.2 + defect p.2 p.1 ∂μ) = 0 := by
    have h := hS.gradient id contDiff_id
    simp only [id_eq] at h
    rw [show (∫ p, angle p.1 p.2 * angle p.1 p.2 ∂μ) = 0 by
      calc
        _ = ∫ _ : Frame n × Frame n, (0 : ℝ) ∂μ :=
          integral_congr_ae (hAzero.mono (fun p hp ↦ by simp [hp]))
        _ = 0 := integral_zero _ _] at h
    simpa using h
  have hT : (∫ p, traceProduct p.1 p.2 ∂μ) = 0 := by
    have h := hS.mixed (fun _ ↦ 1) contDiff_const
    simp only [deriv_const, zero_mul, integral_zero, one_mul, hD] at h
    linarith
  have hlower : ∀ᵐ p ∂μ, (n : ℝ) - 2 ≤
      traceProduct p.1 p.2 + (defect p.1 p.2 + defect p.2 p.1) := by
    filter_upwards [hμ, hAzero] with p hp ha
    rw [traceProduct_eq hp.1 hp.2, ha]
    nlinarith [sq_nonneg (inner ℝ p.1.2 p.2.2)]
  have hle := integral_mono_ae (integrable_const ((n : ℝ) - 2)) (hiT.add hiD) hlower
  change (∫ _ : Frame n × Frame n, (n : ℝ) - 2 ∂μ) ≤
    ∫ p, traceProduct p.1 p.2 + (defect p.1 p.2 + defect p.2 p.1) ∂μ at hle
  rw [integral_add hiT hiD, hT, hD, add_zero, integral_const, smul_eq_mul] at hle
  have hmass : 0 < μ.real univ := by
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    intro hm
    exact hμ0 (Measure.measure_univ_eq_zero.mp hm)
  nlinarith

lemma weighted_trace_lower_bound {n : ℕ} {e f : Frame n}
    (he : IsFrame e) (hf : IsFrame f) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hfc : angle e f ≤ c) (t : ℝ) :
    ((n : ℝ) - 2) * angularWeight t (angle e f) -
        (1 + 3 / (1 - c ^ 2) ^ 2) *
          (angularWeight t (angle e f) * (defect e f + defect f e)) ≤
      angularWeight t (angle e f) * traceProduct e f := by
  by_cases ha : 0 ≤ angle e f
  · have h := mul_le_mul_of_nonneg_left
      (traceProduct_lower_bound he hf hc0 hc1 ha hfc)
      (angularWeight_nonneg t (angle e f))
    nlinarith
  · rw [angularWeight_zero_of_nonpos t (le_of_lt (lt_of_not_ge ha))]
    ring_nf
    exact le_rfl

theorem no_positive_angle_gap {n : ℕ} (hn : 2 < n)
    {μ : Measure (Frame n × Frame n)} [IsFiniteMeasure μ] (hμ0 : μ ≠ 0)
    (hμ : ∀ᵐ p ∂μ, IsFrame p.1 ∧ IsFrame p.2)
    (hS : CoupledStationarity μ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hc : ∀ᵐ p ∂μ, angle p.1 p.2 ≤ c) : False := by
  let k : ℝ := n - 2
  let C : ℝ := 1 + 3 / (1 - c ^ 2) ^ 2
  have hk : 0 < k := by
    have hh : (2 : ℝ) < n := by exact_mod_cast hn
    dsimp [k]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  let t : ℝ := 2 * c * (C + k / 2) / (1 - c) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hcoef : 2 * k * c * (C + k / 2) < t * k * (1 - c) := by
    have hden : 1 - c ≠ 0 := ne_of_gt (sub_pos.mpr hc1)
    dsimp [t]
    field_simp
    nlinarith
  let W : Frame n × Frame n → ℝ := fun p ↦ angularWeight t (angle p.1 p.2)
  let D : Frame n × Frame n → ℝ := fun p ↦ defect p.1 p.2 + defect p.2 p.1
  let dW : Frame n × Frame n → ℝ := fun p ↦ deriv (angularWeight t) (angle p.1 p.2)
  have hW : Continuous W := (angularWeight_contDiff t).continuous.comp continuous_angle
  have hdW : Continuous dW :=
    ((angularWeight_contDiff t).continuous_deriv (by simp)).comp continuous_angle
  have hD : Continuous D := continuous_defect_sum
  have hiW := integrable_pairFrameFunction hμ hW
  have hiWD := integrable_pairFrameFunction hμ (hW.mul hD)
  have hiWA := integrable_pairFrameFunction hμ (hW.mul continuous_angle)
  have hiWT := integrable_pairFrameFunction hμ (hW.mul continuous_traceProduct)
  have hidWD := integrable_pairFrameFunction hμ (hdW.mul hD)
  have hidWC := integrable_pairFrameFunction hμ (hdW.mul continuous_cross)
  have hWnn (p : Frame n × Frame n) : 0 ≤ W p := angularWeight_nonneg _ _
  have hDnn (p : Frame n × Frame n) : 0 ≤ D p :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hdWnn (p : Frame n × Frame n) : 0 ≤ dW p := angularWeight_deriv_nonneg ht.le _
  let J : ℝ := ∫ p, W p ∂μ
  let B : ℝ := ∫ p, W p * D p ∂μ
  let A : ℝ := ∫ p, W p * angle p.1 p.2 ∂μ
  let T : ℝ := ∫ p, W p * traceProduct p.1 p.2 ∂μ
  let Q : ℝ := ∫ p, dW p * cross p.1 p.2 ∂μ
  have hJ : 0 < J := angularWeight_integral_pos hn hμ0 hμ hS t
  have hgrad : (∫ p, dW p * D p ∂μ) = 2 * k * A :=
    hS.gradient _ (angularWeight_contDiff t)
  have hmixed : 2 * T - k * B + 2 * Q = 0 :=
    hS.mixed _ (angularWeight_contDiff t)
  have hA : A ≤ c * J := by
    have hp : ∀ᵐ p ∂μ, W p * angle p.1 p.2 ≤ c * W p := by
      filter_upwards [hc] with p hp
      nlinarith [mul_le_mul_of_nonneg_left hp (hWnn p)]
    have h := integral_mono_ae hiWA (hiW.const_mul c) hp
    simpa only [Pi.mul_apply, integral_const_mul] using h
  have hB : t * B ≤ 2 * k * A := by
    have hp : ∀ᵐ p ∂μ, t * (W p * D p) ≤ dW p * D p :=
      Filter.Eventually.of_forall fun p ↦ by
        have h := mul_le_mul_of_nonneg_right (angularWeight_deriv_lower t (angle p.1 p.2)) (hDnn p)
        simpa only [mul_assoc] using h
    have h := integral_mono_ae (hiWD.const_mul t) hidWD hp
    simpa only [Pi.mul_apply, integral_const_mul, hgrad] using h
  have hQ : -(k * A) ≤ Q := by
    have hp : ∀ᵐ p ∂μ, (-1 / 2 : ℝ) * (dW p * D p) ≤ dW p * cross p.1 p.2 :=
      Filter.Eventually.of_forall fun p ↦ by
        have h := (abs_le.mp (cross_abs_le p.1 p.2)).1
        have hm := mul_le_mul_of_nonneg_left h (hdWnn p)
        dsimp [D] at *
        nlinarith
    have h := integral_mono_ae (hidWD.const_mul (-1 / 2)) hidWC hp
    simp only [Pi.mul_apply] at h
    rw [integral_const_mul, hgrad] at h
    dsimp [Q]
    linarith
  have hT : k * J - C * B ≤ T := by
    have hp : ∀ᵐ p ∂μ, k * W p - C * (W p * D p) ≤ W p * traceProduct p.1 p.2 := by
      filter_upwards [hμ, hc] with p hp hpc
      exact weighted_trace_lower_bound hp.1 hp.2 hc0 hc1 hpc t
    have h := integral_mono_ae ((hiW.const_mul k).sub (hiWD.const_mul C)) hiWT hp
    simp only [Pi.mul_apply, Pi.sub_apply] at h
    have hiCB : Integrable (fun p ↦ C * (W p * D p)) μ := by
      simpa only [Pi.mul_apply] using hiWD.const_mul C
    rw [integral_sub (hiW.const_mul k) hiCB, integral_const_mul,
      integral_const_mul] at h
    exact h
  have hmain : k * (1 - c) * J ≤ (C + k / 2) * B := by
    have hu : T ≤ k / 2 * B + k * A := by linarith
    have hf := mul_le_mul_of_nonneg_left hA hk.le
    nlinarith
  have hB' : t * B ≤ 2 * k * c * J := by
    have h := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 2 * k)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hmain ht.le
  have h2 := mul_le_mul_of_nonneg_left hB' (by positivity : 0 ≤ C + k / 2)
  have h3 := mul_lt_mul_of_pos_right hcoef hJ
  nlinarith

end SphericalFrankel
end RPISingularHarnack

end

end OAI
