import OAI.Probability.Renewal.Annuli
import OAI.Probability.Renewal.Moments

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

lemma exp_bound_from_defect {z : ℂ} {D : ℝ} (_hz : ‖z‖ ≤ 1)
    (hD : 2 * D ≤ 1 - ‖z‖ ^ 2) : ‖z‖ ≤ Real.exp (-D) := by
  have he := Real.add_one_le_exp (-D)
  nlinarith [sq_nonneg (1 - ‖z‖)]

namespace AnnulusData
variable {p : PMF ℕ} {a : ℝ} (D : AnnulusData p a)

def decayConst : ℝ := D.d * D.beta * (2 / Real.pi ^ 2) / (2 * D.M) ^ 2 / 2

lemma decayConst_pos : 0 < D.decayConst := by
  dsimp [decayConst]
  have hM : 0 < D.M := zero_lt_one.trans D.M_one
  positivity [D.d_pos, D.beta_pos, Real.pi_pos]

lemma char_bound {r : ℝ} (hr : 0 < r) (hre : r ≤ D.epsilon)
    {u : ℝ} (hu : 0 ≤ u) (hur : u ≤ r) {t : ℝ} (htr : |t| ≤ r) :
    ‖latticeChar (tilt p u hu) t‖ ≤ Real.exp (-D.decayConst * r ^ (a - 2) * t ^ 2) := by
  let L := r⁻¹ / (2 * D.M)
  have hM : 0 < D.M := zero_lt_one.trans D.M_one
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hrect := rectangle_defect_bound (tilt p u hu) t
    ((2 / Real.pi ^ 2) * L ^ 2 * t ^ 2) (annulus D.M r) {D.b} (by
      intro j hj l hl
      rw [mem_singleton_iff] at hl
      subst l
      obtain ⟨hlow, hupp⟩ := D.geometry r hr hre j hj
      have hn : 0 ≤ (j : ℝ) - D.b := hL.trans hlow
      have habs : |((j : ℝ) - D.b) * t| ≤ Real.pi := by
        rw [abs_mul, abs_of_nonneg hn]
        calc
          ((j : ℝ) - D.b) * |t| ≤ r⁻¹ * r := mul_le_mul hupp htr (abs_nonneg _) (inv_nonneg.mpr hr.le)
          _ = 1 := inv_mul_cancel₀ hr.ne'
          _ ≤ Real.pi := (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
      have hsq : L ^ 2 ≤ ((j : ℝ) - D.b) ^ 2 := sq_le_sq₀ hL hn |>.mpr hlow
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq (sq_nonneg t))
        (by positivity : 0 ≤ 2 / Real.pi ^ 2)
      have hc := Real.cos_le_one_sub_mul_cos_sq habs
      rw [mul_pow] at hc
      nlinarith)
  have hmass := D.mass r hr hre u hu hur
  have hatom := D.atom r hr hre u hu hur
  have hn : 0 ≤ (2 / Real.pi ^ 2) * L ^ 2 * t ^ 2 := by positivity
  have hmulti := mul_le_mul_of_nonneg_right (mul_le_mul hmass hatom D.beta_pos.le measureReal_nonneg) hn
  have hdef := hmulti.trans hrect
  simp only [neg_mul]
  apply exp_bound_from_defect (norm_latticeChar_le_one _ _)
  have hid : 2 * (D.decayConst * r ^ (a - 2) * t ^ 2) =
      (D.d * r ^ a) * D.beta * ((2 / Real.pi ^ 2) * L ^ 2 * t ^ 2) := by
    dsimp [decayConst, L]
    rw [Real.rpow_sub hr, Real.rpow_two]
    field_simp
  rw [hid]
  exact hdef

lemma intermediate {t : ℝ} (ht : 0 < |t|) (hte : |t| ≤ D.epsilon)
    {u : ℝ} (hu : 0 ≤ u) (hut : u ≤ |t|) :
    ‖latticeChar (tilt p u hu) t‖ ≤ Real.exp (-D.decayConst * |t| ^ a) := by
  have hh := D.char_bound ht hte hu hut le_rfl
  have hid : |t| ^ (a - 2) * t ^ 2 = |t| ^ a := by
    rw [Real.rpow_sub ht, Real.rpow_two, sq_abs]
    have htn : t ≠ 0 := abs_pos.mp ht
    field_simp
  simpa only [mul_assoc, hid] using hh

lemma original_small (ha : 0 < a) {t : ℝ} (ht : |t| ≤ D.epsilon) :
    ‖latticeChar p t‖ ≤ Real.exp (-D.decayConst * |t| ^ a) := by
  by_cases hzero : t = 0
  · subst t
    rw [abs_zero, Real.zero_rpow ha.ne']
    simp [latticeChar]
  · have ht0 : 0 < |t| := abs_pos.mpr hzero
    simpa only [tilt_zero] using D.intermediate ht0 ht (u := 0) le_rfl ht0.le

end AnnulusData

lemma tilt_spectral_gap (p : PMF ℕ) (hspan : SpanOne p) {a : ℝ} (ha : 0 < a)
    (hpow : BoundedPowerInput p a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ ∈ Ico (0 : ℝ) 1, ∃ ε > (0 : ℝ), ∀ u (hu : 0 ≤ u), u ≤ ε →
      ∀ t, δ ≤ |t| → |t| ≤ Real.pi → ‖latticeChar (tilt p u hu) t‖ ≤ ρ := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := lattice_spectral_gap p hspan hδ
  obtain ⟨ε, hε, he⟩ := laplace_small p ha hpow
  rcases hpow with ⟨c, hc, C, hC, x₀, hx₀, _, hL⟩
  have hlim : Tendsto (fun u : ℝ => 4 * C * u ^ a) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const ha.le).tendsto 0).const_mul (4 * C)
    simpa [Real.zero_rpow ha.ne'] using h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u : ℝ in 𝓝[>] 0, 4 * C * u ^ a < (1 - ρ) / 2 :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨η, hη, heη⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨(1 + ρ) / 2, ⟨by linarith, by linarith⟩,
    min η (min ε x₀⁻¹), lt_min hη (lt_min hε (inv_pos.mpr hx₀)), ?_⟩
  intro u hu hue t ht htp
  rcases hu.eq_or_lt with hzero | hu
  · subst u
    rw [tilt_zero]
    exact (hρ t ht htp).trans (by linarith)
  · have hlu := (hL u hu (hue.trans ((min_le_right _ _).trans (min_le_right _ _)))).2
    have hlz := he u hu (hue.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hηu := heη ⟨hu, hue.trans (min_le_left _ _)⟩
    change 4 * C * u ^ a < (1 - ρ) / 2 at hηu
    have hdiff := tilt_char_difference p u hu.le t
    have hzpos := laplace_pos p hu.le
    have hdef : 0 ≤ 1 - laplace p u := sub_nonneg.mpr (laplace_le_one p hu.le)
    have hquot : 2 * (1 - laplace p u) / laplace p u ≤ 4 * C * u ^ a := by
      apply (div_le_iff₀ hzpos).mpr
      have hmul := mul_le_mul_of_nonneg_left hlz (by positivity : 0 ≤ 4 * C * u ^ a)
      nlinarith
    have htri := norm_le_norm_add_norm_sub (latticeChar p t) (latticeChar (tilt p u hu.le) t)
    rw [norm_sub_rev] at htri
    have horig := hρ t ht htp
    linarith

end HoneycombLocal

end

end OAI
