import OAI.Analysis.Mahler.ConformalSeries
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! Angular geometry of the conformal series. -/

noncomputable section
open Complex Set Metric
open scoped Topology
namespace MahlerConformal

def polar (r θ : ℝ) : ℂ := r * Complex.exp (θ * I)
def Q (r θ : ℝ) : ℝ := (F (polar r θ)).re
def S (r θ : ℝ) : ℝ := (F (polar r θ)).im
def B (r θ : ℝ) : ℝ := 4 / Real.pi^2 * Real.arctan (2*r*Real.sin θ/(1-r^2))

lemma norm_polar {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖polar r θ‖ = r := by
  simp [polar, Complex.norm_exp, abs_of_nonneg hr]

lemma polar_ne_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : polar r θ ≠ 0 := by
  exact norm_pos_iff.mp (by rw [norm_polar hr.le]; exact hr)

lemma polar_re (r θ : ℝ) : (polar r θ).re = r * Real.cos θ := by
  simp [polar]

lemma polar_im (r θ : ℝ) : (polar r θ).im = r * Real.sin θ := by
  simp [polar]

lemma hasDerivAt_polar_complex (r : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℂ => (r : ℂ) * Complex.exp (t * I))
      (I * ((r : ℂ) * Complex.exp (z * I))) z := by
  simpa only [id_eq, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using
    (((hasDerivAt_id z).mul_const I).cexp.const_mul (r : ℂ))

lemma hasDerivAt_Q_arg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    HasDerivAt (Q r) (-(4 / Real.pi^2) * (cayley (polar r θ)).arg) θ := by
  have hw : ‖polar r θ‖ < 1 := by rwa [norm_polar hr.le]
  have hd := ((hasDerivAt_F_log hw (polar_ne_zero hr θ)).comp (θ : ℂ)
    (hasDerivAt_polar_complex r θ)).real_of_complex
  have he : (4 / ((Real.pi : ℂ)^2 * polar r θ) * Complex.log (cayley (polar r θ))) *
      (I * polar r θ) = (4 / (Real.pi : ℂ)^2) * I * Complex.log (cayley (polar r θ)) := by
    field_simp [polar_ne_zero hr θ]
  change HasDerivAt (Q r) _ θ at hd
  change HasDerivAt (Q r) ((4 / ((Real.pi : ℂ)^2 * polar r θ) *
    Complex.log (cayley (polar r θ))) * (I * polar r θ)).re θ at hd
  rw [he] at hd
  simpa [Complex.mul_re, Complex.log_im, ← Complex.ofReal_pow, ← Complex.ofReal_div] using hd

/-- The principal branch gives arctan, rather than an angle modulo pi. -/
lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm

lemma cayley_im_div_re {w : ℂ} (hw : ‖w‖ < 1) :
    (cayley w).im / (cayley w).re = 2*w.im/(1-‖w‖^2) := by
  have hden : Complex.normSq (1-w) ≠ 0 :=
    (Complex.normSq_pos.mpr (one_sub_ne hw)).ne'
  have hs : ‖w‖^2 = w.re^2 + w.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hn : 1-‖w‖^2 ≠ 0 := by nlinarith [norm_nonneg w]
  have hre : (cayley w).re = (1-‖w‖^2)/Complex.normSq (1-w) := by
    simp only [cayley, Complex.div_re, Complex.add_re, Complex.sub_re,
      Complex.one_re, Complex.add_im, Complex.sub_im, Complex.one_im]
    rw [hs]
    ring
  have him : (cayley w).im = 2*w.im/Complex.normSq (1-w) := by
    simp only [cayley, Complex.div_im, Complex.add_re, Complex.sub_re,
      Complex.one_re, Complex.add_im, Complex.sub_im, Complex.one_im]
    ring
  rw [hre, him]
  field_simp

/-- The branch-sensitive angular identity. -/
theorem arg_cayley_polar {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (cayley (polar r θ)).arg = Real.arctan (2*r*Real.sin θ/(1-r^2)) := by
  have hw : ‖polar r θ‖ < 1 := by rwa [norm_polar hr.le]
  rw [arg_eq_arctan_of_re_pos (cayley_re_pos hw), cayley_im_div_re hw,
    norm_polar hr.le, polar_im]
  congr 1
  ring

/-- The derivative of the series' real part is minus B. -/
theorem hasDerivAt_Q {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    HasDerivAt (Q r) (-B r θ) θ := by
  simpa only [arg_cayley_polar hr hr1, B, neg_mul] using hasDerivAt_Q_arg hr hr1 θ

theorem neg_deriv_Q_eq_B {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    -deriv (Q r) θ = B r θ := by rw [(hasDerivAt_Q hr hr1 θ).deriv, neg_neg]

theorem B_pos {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) : 0 < B r θ := by
  unfold B
  apply mul_pos (div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
  apply Real.arctan_pos.mpr
  exact div_pos (mul_pos (mul_pos (by norm_num) hr) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ))
    (by nlinarith)

theorem B_lt_two_div_pi (r θ : ℝ) : B r θ < 2 / Real.pi := by
  have h := mul_lt_mul_of_pos_left (Real.arctan_lt_pi_div_two (2*r*Real.sin θ/(1-r^2)))
    (show 0 < 4 / Real.pi^2 by positivity)
  have he : 4 / Real.pi^2 * (Real.pi/2) = 2/Real.pi := by field_simp; ring
  simpa only [B, he] using h

/-- Strict decrease includes the semicircle endpoints, whose derivatives vanish. -/
theorem Q_strictAntiOn {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    StrictAntiOn (Q r) (Icc 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun θ _ => (hasDerivAt_Q hr hr1 θ).continuousAt.continuousWithinAt)
  intro θ hθ
  rw [interior_Icc] at hθ
  rw [(hasDerivAt_Q hr hr1 θ).deriv]
  exact neg_neg_of_pos (B_pos hr hr1 hθ.1 hθ.2)

lemma polar_zero (r : ℝ) : polar r 0 = (r : ℂ) := by simp [polar]

lemma polar_pi (r : ℝ) : polar r Real.pi = -(r : ℂ) := by simp [polar]

lemma polar_pi_sub (r θ : ℝ) : polar r (Real.pi-θ) = -starRingEnd ℂ (polar r θ) := by
  apply Complex.ext <;> simp [polar_re, polar_im, Real.cos_pi_sub, Real.sin_pi_sub]

lemma F_real_im (r : ℝ) : (F (r : ℂ)).im = 0 := by
  have h := congrArg Complex.im (F_conj (r : ℂ))
  simp only [Complex.conj_ofReal, Complex.conj_im] at h
  linarith

theorem Q_zero (r : ℝ) : Q r 0 = (F (r : ℂ)).re := by rw [Q, polar_zero]

theorem Q_pi (r : ℝ) : Q r Real.pi = -(F (r : ℂ)).re := by
  rw [Q, polar_pi, F_odd, Complex.neg_re]

theorem Q_pi_sub (r θ : ℝ) : Q r (Real.pi-θ) = -Q r θ := by
  simp only [Q, polar_pi_sub, F_odd, F_conj, Complex.neg_re, Complex.conj_re]

theorem Q_pi_div_two (r : ℝ) : Q r (Real.pi/2) = 0 := by
  have h := Q_pi_sub r (Real.pi/2)
  rw [show Real.pi-Real.pi/2 = Real.pi/2 by ring] at h
  linarith

theorem S_zero (r : ℝ) : S r 0 = 0 := by rw [S, polar_zero, F_real_im]

theorem S_pi (r : ℝ) : S r Real.pi = 0 := by
  rw [S, polar_pi, F_odd, Complex.neg_im, F_real_im, neg_zero]

theorem Q_mem_Ioo {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Q r θ ∈ Ioo (-(F (r : ℂ)).re) (F (r : ℂ)).re := by
  have ha := Q_strictAntiOn hr hr1
  constructor
  · simpa only [Q_pi] using ha ⟨hθ.le, hθπ.le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hθπ
  · simpa only [Q_zero] using ha ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.le, hθπ.le⟩ hθ

/-- Existence and uniqueness of the angle at a fixed radius.
The endpoint condition is stated with F(r) itself, with no radial theorem assumed. -/
theorem existsUnique_angle {r q : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hq : -(F (r : ℂ)).re < q) (hq' : q < (F (r : ℂ)).re) :
    ∃! θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ Q r θ = q := by
  have hcont : ContinuousOn (Q r) (Icc 0 Real.pi) :=
    fun θ _ => (hasDerivAt_Q hr hr1 θ).continuousAt.continuousWithinAt
  obtain ⟨θ, hθ, he⟩ := intermediate_value_Icc' Real.pi_pos.le hcont
    (show q ∈ Icc (Q r Real.pi) (Q r 0) by simpa [Q_zero, Q_pi] using And.intro hq.le hq'.le)
  have hi : θ ∈ Ioo 0 Real.pi := by
    constructor
    · refine lt_of_le_of_ne hθ.1 ?_
      intro h
      subst θ
      rw [Q_zero] at he
      linarith
    · refine lt_of_le_of_ne hθ.2 ?_
      intro h
      subst θ
      rw [Q_pi] at he
      linarith
  refine ⟨θ, ⟨hi, he⟩, ?_⟩
  intro φ hφ
  exact (Q_strictAntiOn hr hr1).injOn ⟨hφ.1.1.le, hφ.1.2.le⟩ hθ (hφ.2.trans he.symm)

theorem Q_pos_iff {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) : 0 < Q r θ ↔ θ < Real.pi/2 := by
  have hm : Real.pi/2 ∈ Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  constructor
  · intro h
    by_contra hn
    have hle := (Q_strictAntiOn hr hr1).antitoneOn hm hθ (le_of_not_gt hn)
    rw [Q_pi_div_two] at hle
    linarith
  · intro h
    simpa only [Q_pi_div_two] using Q_strictAntiOn hr hr1 hθ hm h

/-- Reflection reduces an upper-semicircle angle to [0, pi/2], and Q to |Q|. -/
theorem Q_min_angle {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Q r (min θ (Real.pi-θ)) = |Q r θ| := by
  by_cases h : θ ≤ Real.pi/2
  · rw [min_eq_left (by linarith)]
    apply (abs_of_nonneg _).symm
    have hh := (Q_strictAntiOn hr hr1).antitoneOn hθ
      (show Real.pi/2 ∈ Icc (0 : ℝ) Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩) h
    simpa only [Q_pi_div_two] using hh
  · rw [min_eq_right (by linarith), Q_pi_sub]
    apply (abs_of_nonpos _).symm
    have hh := (Q_strictAntiOn hr hr1).antitoneOn
      (show Real.pi/2 ∈ Icc (0 : ℝ) Real.pi from ⟨by positivity, by linarith [Real.pi_pos]⟩)
      hθ (by linarith)
    simpa only [Q_pi_div_two] using hh

end MahlerConformal

end

end OAI
