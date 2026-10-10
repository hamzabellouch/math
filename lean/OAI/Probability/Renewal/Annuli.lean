import OAI.Probability.Renewal.Tilt

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

def annulus (M r : ℝ) : Set ℕ := {j | r⁻¹ / M < (j : ℝ) ∧ (j : ℝ) ≤ r⁻¹}

structure AnnulusData (p : PMF ℕ) (a : ℝ) where
  M : ℝ
  M_one : 1 < M
  d : ℝ
  d_pos : 0 < d
  b : ℕ
  beta : ℝ
  beta_pos : 0 < beta
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  mass : ∀ r, 0 < r → r ≤ epsilon → ∀ u (hu : 0 ≤ u), u ≤ r →
    d * r ^ a ≤ (tilt p u hu).toMeasure.real (annulus M r)
  atom : ∀ r, 0 < r → r ≤ epsilon → ∀ u (hu : 0 ≤ u), u ≤ r →
    beta ≤ (tilt p u hu).toMeasure.real {b}
  geometry : ∀ r, 0 < r → r ≤ epsilon → ∀ j ∈ annulus M r,
    r⁻¹ / (2 * M) ≤ (j : ℝ) - b ∧ (j : ℝ) - b ≤ r⁻¹

lemma annulusData_exists (p : PMF ℕ) {a : ℝ} (ha : 0 < a ∧ a < 1)
    (hpower : BoundedPowerInput p a) : Nonempty (AnnulusData p a) := by
  obtain ⟨M, hM, c, hc, hann⟩ := annular_mass p ha hpower
  obtain ⟨X, hX⟩ := eventually_atTop.mp hann
  obtain ⟨b, hb⟩ := p.support_nonempty
  have hbpos : 0 < (p b).toReal := ENNReal.toReal_pos (by simpa using hb) (p.apply_ne_top b)
  have hM0 : 0 < M := zero_lt_one.trans hM
  let R := max X (max 1 (2 * M * b))
  have hR : 0 < R := zero_lt_one.trans_le ((le_max_left _ _).trans (le_max_right _ _))
  have hRb : (b : ℝ) ≤ R := by
    have h : 2 * M * (b : ℝ) ≤ R := (le_max_right _ _).trans (le_max_right _ _)
    nlinarith [Nat.cast_nonneg (α := ℝ) b]
  have hrR {r : ℝ} (hr : 0 < r) (hre : r ≤ R⁻¹) : R ≤ r⁻¹ := by
    exact (le_inv_comm₀ hR hr).mpr hre
  have hscale {r u : ℝ} (hr : 0 < r) (hur : u ≤ r) : u * r⁻¹ ≤ 1 := by
    calc u * r⁻¹ ≤ r * r⁻¹ := mul_le_mul_of_nonneg_right hur (inv_nonneg.mpr hr.le)
         _ = 1 := mul_inv_cancel₀ hr.ne'
  refine ⟨⟨M, hM, Real.exp (-1) * c, by positivity, b,
    Real.exp (-1) * (p b).toReal, by positivity, R⁻¹, inv_pos.mpr hR, ?_, ?_, ?_⟩⟩
  · intro r hr hre u hu hur
    have hRm := hrR hr hre
    have hm := hX r⁻¹ ((le_max_left _ _).trans hRm)
    have hpw : (r⁻¹) ^ (-a) = r ^ a := by
      rw [Real.inv_rpow hr.le, Real.rpow_neg hr.le, inv_inv]
    rw [hpw] at hm
    have hlo := measureReal_tilt_lower p u hu (annulus M r) r⁻¹ (fun j hj => hj.2)
    have hexp : Real.exp (-1) ≤ Real.exp (-u * r⁻¹) := by
      apply Real.exp_le_exp.mpr
      linarith [hscale hr hur]
    calc
      Real.exp (-1) * c * r ^ a = Real.exp (-1) * (c * r ^ a) := by ring
      _ ≤ Real.exp (-1) * p.toMeasure.real (annulus M r) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
      _ ≤ Real.exp (-u * r⁻¹) * p.toMeasure.real (annulus M r) := by gcongr
      _ ≤ _ := hlo
  · intro r hr hre u hu hur
    have hRm := hrR hr hre
    have hbR : (b : ℝ) ≤ r⁻¹ := hRb.trans hRm
    have hlo := measureReal_tilt_lower p u hu {b} (b : ℝ) (by intro j hj; rw [Set.mem_singleton_iff] at hj; subst j; rfl)
    have hexp : Real.exp (-1) ≤ Real.exp (-u * (b : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hbR hu
      linarith [hscale hr hur]
    have hsingle : p.toMeasure.real {b} = (p b).toReal := by
      rw [Measure.real, p.toMeasure_apply_singleton _ (measurableSet_singleton _)]
    rw [hsingle] at hlo
    exact (mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg).trans hlo
  · intro r hr hre j hj
    have hRm := hrR hr hre
    have hRb' : 2 * M * (b : ℝ) ≤ r⁻¹ := ((le_max_right _ _).trans (le_max_right _ _)).trans hRm
    have hbsmall : (b : ℝ) ≤ r⁻¹ / (2 * M) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    have hlow := hj.1
    have hid : r⁻¹ / M = 2 * (r⁻¹ / (2 * M)) := by field_simp
    rw [hid] at hlow
    constructor
    · linarith
    · linarith [hj.2, Nat.cast_nonneg (α := ℝ) b]

lemma tilt_zero (p : PMF ℕ) : tilt p 0 le_rfl = p := by
  ext j
  rw [tilt_apply]
  simp [laplace]

end HoneycombLocal

end

end OAI
