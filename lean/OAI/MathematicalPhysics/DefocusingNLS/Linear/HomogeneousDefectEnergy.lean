import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRadialDefect
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # A power lower bound for a nonzero transverse radial defect

The large imaginary diagonal in the radial equation does not enter this
energy estimate. An integrable `O(r⁻³)` perturbation only changes the
positive lower-bound constant, not the radial power.
-/

open Set Filter Topology

namespace DefocusingNLS

local notation "V" => ℂ × ℂ

noncomputable def homogeneousPairEnergy (w : V) : ℝ :=
  Complex.normSq w.1 + Complex.normSq w.2

noncomputable def homogeneousPairReal (u v : V) : ℝ :=
  (star u.1 * v.1 + star u.2 * v.2).re

theorem homogeneousPairEnergy_nonneg (w : V) : 0 ≤ homogeneousPairEnergy w := by
  unfold homogeneousPairEnergy
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem homogeneousPairEnergy_eq_norms (w : V) :
    homogeneousPairEnergy w = ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 := by
  simp only [homogeneousPairEnergy, Complex.normSq_eq_norm_sq]

theorem homogeneousPairEnergy_lower (w : V) : ‖w‖ ^ 2 ≤ homogeneousPairEnergy w := by
  rw [Prod.norm_def, homogeneousPairEnergy_eq_norms]
  rcases le_total ‖w.1‖ ‖w.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖w.1‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖w.2‖]

theorem homogeneousPairEnergy_upper (w : V) : homogeneousPairEnergy w ≤ 2 * ‖w‖ ^ 2 := by
  rw [homogeneousPairEnergy_eq_norms]
  have h₁ := (sq_le_sq₀ (norm_nonneg w.1) (norm_nonneg w)).2 (norm_fst_le w)
  have h₂ := (sq_le_sq₀ (norm_nonneg w.2) (norm_nonneg w)).2 (norm_snd_le w)
  linarith

theorem homogeneousPairEnergy_pos {w : V} (hw : w ≠ 0) :
    0 < homogeneousPairEnergy w :=
  lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hw)) (homogeneousPairEnergy_lower w)

theorem homogeneousPairReal_bound (u v : V) :
    |homogeneousPairReal u v| ≤ 2 * ‖u‖ * ‖v‖ := by
  calc
    |homogeneousPairReal u v| ≤ ‖star u.1 * v.1 + star u.2 * v.2‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖star u.1 * v.1‖ + ‖star u.2 * v.2‖ := norm_add_le _ _
    _ = ‖u.1‖ * ‖v.1‖ + ‖u.2‖ * ‖v.2‖ := by simp only [norm_mul, norm_star]
    _ ≤ ‖u‖ * ‖v‖ + ‖u‖ * ‖v‖ := add_le_add
      (mul_le_mul (norm_fst_le u) (norm_fst_le v) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (norm_snd_le u) (norm_snd_le v) (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖u‖ * ‖v‖ := by ring

theorem homogeneousComplexNormSq_hasDerivAt {u : ℝ → ℂ} {v : ℂ} {r : ℝ}
    (hu : HasDerivAt u v r) :
    HasDerivAt (fun t => Complex.normSq (u t)) (2 * (star (u r) * v).re) r := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hu.star.mul hu)
  convert! h using 1
  · ext t
    simp [Complex.normSq_apply, Complex.mul_re]
  · simp only [Complex.reCLM_apply, Complex.add_re, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring

theorem homogeneousPairEnergy_hasDerivAt {w : ℝ → V} {v : V} {r : ℝ}
    (hw : HasDerivAt w v r) :
    HasDerivAt (fun t => homogeneousPairEnergy (w t))
      (2 * homogeneousPairReal (w r) v) r := by
  convert! (homogeneousComplexNormSq_hasDerivAt (homogeneousPair_fst_hasDerivAt hw)).add
    (homogeneousComplexNormSq_hasDerivAt (homogeneousPair_snd_hasDerivAt hw)) using 1
  simp only [homogeneousPairReal, Complex.add_re]
  ring

theorem homogeneousPairReal_damping (w e : V) (d omega₁ omega₂ : ℝ) :
    homogeneousPairReal w
      (-((d : ℂ) + Complex.I * omega₁) * w.1 - e.1,
        -((d : ℂ) + Complex.I * omega₂) * w.2 - e.2) =
      -d * homogeneousPairEnergy w - homogeneousPairReal w e := by
  simp only [homogeneousPairReal, homogeneousPairEnergy, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem homogeneousPairEnergy_damping_lower (w e : V) (d omega₁ omega₂ M r : ℝ)
    (hM : 0 ≤ M) (hr : 0 < r) (he : ‖e‖ ≤ M / r ^ 3 * ‖w‖) :
    -(2 * d / r + 4 * M / r ^ 3) * homogeneousPairEnergy w ≤
      2 * homogeneousPairReal w
        (-(((d / r : ℝ) : ℂ) + Complex.I * omega₁) * w.1 - e.1,
          -(((d / r : ℝ) : ℂ) + Complex.I * omega₂) * w.2 - e.2) := by
  rw [homogeneousPairReal_damping]
  have hR : homogeneousPairReal w e ≤ 2 * (M / r ^ 3) * homogeneousPairEnergy w := by
    calc
      homogeneousPairReal w e ≤ |homogeneousPairReal w e| := le_abs_self _
      _ ≤ 2 * ‖w‖ * ‖e‖ := homogeneousPairReal_bound w e
      _ ≤ 2 * ‖w‖ * (M / r ^ 3 * ‖w‖) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * (M / r ^ 3) * ‖w‖ ^ 2 := by ring
      _ ≤ 2 * (M / r ^ 3) * homogeneousPairEnergy w :=
        mul_le_mul_of_nonneg_left (homogeneousPairEnergy_lower w) (by positivity)
  have heq : -(2 * d / r + 4 * M / r ^ 3) * homogeneousPairEnergy w =
      2 * (-(d / r) * homogeneousPairEnergy w -
        2 * (M / r ^ 3) * homogeneousPairEnergy w) := by ring
  rw [heq]
  linarith

noncomputable def homogeneousDefectWeight (d M r : ℝ) : ℝ :=
  Real.exp (2 * d * Real.log r - 2 * M / r ^ 2)

theorem homogeneousDefectWeight_hasDerivAt (d M r : ℝ) (hr : 0 < r) :
    HasDerivAt (homogeneousDefectWeight d M)
      ((2 * d / r + 4 * M / r ^ 3) * homogeneousDefectWeight d M r) r := by
  have hlog := (Real.hasDerivAt_log hr.ne').const_mul (2 * d)
  have hinv := ((hasDerivAt_id r).pow 2).inv (pow_ne_zero 2 hr.ne')
  have h := (hlog.sub (hinv.const_mul (2 * M))).exp
  apply h.congr_deriv
  change homogeneousDefectWeight d M r *
      (2 * d * r⁻¹ - 2 * M * (-(2 * r ^ (2 - 1) * 1) / (r ^ 2) ^ 2)) =
    (2 * d / r + 4 * M / r ^ 3) * homogeneousDefectWeight d M r
  rw [mul_comm (homogeneousDefectWeight d M r)]
  congr 1
  norm_num
  field_simp [hr.ne']
  ring

theorem homogeneousDefectWeight_pos (d M r : ℝ) : 0 < homogeneousDefectWeight d M r :=
  Real.exp_pos _

theorem homogeneousDefectWeight_le (d M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) :
    homogeneousDefectWeight d M r ≤ r ^ (2 * d) := by
  rw [Real.rpow_def_of_pos hr]
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ 2 * M / r ^ 2 := by positivity
  nlinarith

/-- The normalized squared defect is monotone on every positive tail. -/
theorem homogeneousDefectEnergy_monotone (E E' : ℝ → ℝ) (d M R : ℝ)
    (hR : 0 < R) (hE : ∀ r, R ≤ r → HasDerivAt E (E' r) r)
    (hlower : ∀ r, R ≤ r → -(2 * d / r + 4 * M / r ^ 3) * E r ≤ E' r) :
    MonotoneOn (fun r => homogeneousDefectWeight d M r * E r) (Ici R) := by
  have hd : ∀ r, R ≤ r → HasDerivAt
      (fun t => homogeneousDefectWeight d M t * E t)
      (homogeneousDefectWeight d M r *
        ((2 * d / r + 4 * M / r ^ 3) * E r + E' r)) r := by
    intro r hr
    convert! (homogeneousDefectWeight_hasDerivAt d M r (hR.trans_le hr)).mul (hE r hr) using 1
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici R)
  · intro r hr
    exact (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    exact (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [(hd r (interior_subset hr)).deriv]
    apply mul_nonneg (homogeneousDefectWeight_pos d M r).le
    linarith [hlower r (interior_subset hr)]

/-- A positive squared defect stays above a positive multiple of its radial power. -/
theorem homogeneousDefectEnergy_power_lower (E E' : ℝ → ℝ) (d M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 < R) (hE0 : 0 < E R)
    (hEn : ∀ r, R ≤ r → 0 ≤ E r)
    (hE : ∀ r, R ≤ r → HasDerivAt E (E' r) r)
    (hlower : ∀ r, R ≤ r → -(2 * d / r + 4 * M / r ^ 3) * E r ≤ E' r) :
    ∃ c : ℝ, 0 < c ∧ ∀ r, R ≤ r → c ≤ r ^ (2 * d) * E r := by
  refine ⟨homogeneousDefectWeight d M R * E R,
    mul_pos (homogeneousDefectWeight_pos d M R) hE0, ?_⟩
  intro r hr
  exact ((homogeneousDefectEnergy_monotone E E' d M R hR hE hlower)
    (show R ∈ Ici R by simp only [mem_Ici, le_refl]) hr hr).trans
      (mul_le_mul_of_nonneg_right
        (homogeneousDefectWeight_le d M r hM (hR.trans_le hr)) (hEn r hr))

theorem homogeneousDefect_nonzero_power_bound
    (W e : ℝ → V) (omega₁ omega₂ : ℝ → ℝ) (d M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 < R) (hW0 : W R ≠ 0)
    (hW : ∀ r, R ≤ r → HasDerivAt W
      (-(((d / r : ℝ) : ℂ) + Complex.I * omega₁ r) * (W r).1 - (e r).1,
        -(((d / r : ℝ) : ℂ) + Complex.I * omega₂ r) * (W r).2 - (e r).2) r)
    (he : ∀ r, R ≤ r → ‖e r‖ ≤ M / r ^ 3 * ‖W r‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ r, R ≤ r →
      c ≤ r ^ (2 * d) * homogeneousPairEnergy (W r) := by
  apply homogeneousDefectEnergy_power_lower
    (fun r => homogeneousPairEnergy (W r))
    (fun r => 2 * homogeneousPairReal (W r)
      (-(((d / r : ℝ) : ℂ) + Complex.I * omega₁ r) * (W r).1 - (e r).1,
        -(((d / r : ℝ) : ℂ) + Complex.I * omega₂ r) * (W r).2 - (e r).2))
    d M R hM hR (homogeneousPairEnergy_pos hW0)
    (fun r _ => homogeneousPairEnergy_nonneg (W r))
  · intro r hr
    exact homogeneousPairEnergy_hasDerivAt (hW r hr)
  · intro r hr
    exact homogeneousPairEnergy_damping_lower (W r) (e r) d (omega₁ r) (omega₂ r)
      M r hM (hR.trans_le hr) (he r hr)

end DefocusingNLS

end OAI
