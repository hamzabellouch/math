import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.NormalizationProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.GaussianFrequencyProgram

namespace OAI

/-! Stability of the exact fixed normalization factor ω/(A²π). -/

noncomputable section
namespace ContinuumCoulomb

theorem guarded_inverse_error {C a a' ε : ℝ} (hC : 0 < C) (ha : 0 < a)
    (hguard : 2 ≤ C * a) (hε : 0 ≤ ε) (hsmall : C * ε ≤ 1)
    (he : |a' - a| ≤ ε) :
    0 < a' ∧ a⁻¹ ≤ C ∧ a'⁻¹ ≤ C ∧ |a'⁻¹ - a⁻¹| ≤ C ^ 2 * ε := by
  have hl := mul_le_mul_of_nonneg_left (abs_le.mp he).1 hC.le
  have hguard' : 1 ≤ C * a' := by nlinarith
  have ha' : 0 < a' := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt hn)
    linarith
  have hi : a⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha).mpr (by linarith)
  have hi' : a'⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha').mpr hguard'
  refine ⟨ha', hi, hi', ?_⟩
  have hid : a'⁻¹ - a⁻¹ = (a - a') * a'⁻¹ * a⁻¹ := by
    field_simp [ha.ne', ha'.ne']
  rw [hid, abs_mul, abs_mul, abs_sub_comm a a',
    abs_of_pos (inv_pos.mpr ha'), abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ ε * C * C := by gcongr
    _ = _ := by ring

theorem coulomb_normalization_error {C a a' p p' f f' ε : ℝ}
    (hC : 1 ≤ C) (ha : 0 < a) (hp : 0 < p)
    (hga : 2 ≤ C * a) (hgp : 2 ≤ C * p) (hf : |f| ≤ C)
    (hε : 0 ≤ ε) (hsmall : C * ε ≤ 1)
    (hea : |a' - a| ≤ ε) (hep : |p' - p| ≤ ε) (hef : |f' - f| ≤ ε) :
    |f' / (a' ^ 2 * p') - f / (a ^ 2 * p)| ≤ (C ^ 3 + 3 * C ^ 5) * ε := by
  have hC0 : 0 < C := by linarith
  obtain ⟨ha', hia, hia', heia⟩ := guarded_inverse_error hC0 ha hga hε hsmall hea
  obtain ⟨hp', hip, hip', heip⟩ := guarded_inverse_error hC0 hp hgp hε hsmall hep
  have hsq : |a'⁻¹ ^ 2 - a⁻¹ ^ 2| ≤ 2 * C ^ 3 * ε := by
    have hid : a'⁻¹ ^ 2 - a⁻¹ ^ 2 = (a'⁻¹ - a⁻¹) * (a'⁻¹ + a⁻¹) := by ring
    rw [hid, abs_mul, abs_of_pos (add_pos (inv_pos.mpr ha') (inv_pos.mpr ha))]
    calc
      _ ≤ (C ^ 2 * ε) * (C + C) := by gcongr
      _ = _ := by ring
  have hid : f' / (a' ^ 2 * p') - f / (a ^ 2 * p) =
      (f' - f) * a'⁻¹ ^ 2 * p'⁻¹ +
        f * (a'⁻¹ ^ 2 - a⁻¹ ^ 2) * p'⁻¹ +
        f * a⁻¹ ^ 2 * (p'⁻¹ - p⁻¹) := by
    field_simp [ha.ne', ha'.ne', hp.ne', hp'.ne']
    ring
  have h1 : |(f' - f) * a'⁻¹ ^ 2 * p'⁻¹| ≤ C ^ 3 * ε := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a'⁻¹), abs_of_pos (inv_pos.mpr hp')]
    calc
      _ ≤ ε * C ^ 2 * C := by gcongr
      _ = _ := by ring
  have h2 : |f * (a'⁻¹ ^ 2 - a⁻¹ ^ 2) * p'⁻¹| ≤ 2 * C ^ 5 * ε := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hp')]
    calc
      _ ≤ C * (2 * C ^ 3 * ε) * C := by gcongr
      _ = _ := by ring
  have h3 : |f * a⁻¹ ^ 2 * (p'⁻¹ - p⁻¹)| ≤ C ^ 5 * ε := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg a⁻¹)]
    calc
      _ ≤ C * C ^ 2 * (C ^ 2 * ε) := by gcongr
      _ = _ := by ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add h1 h2) h3).trans_eq (by ring))

end ContinuumCoulomb

end

end OAI
