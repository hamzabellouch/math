import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeTaylor

namespace OAI

/-! The actual free tail is strictly subunit immediately after its initial radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_modulus_lt_one (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hF : ∀ r ∈ Icc l u, F r=1+∫ t in l..r, G t)
    (hG : ∀ r ∈ Icc l u, G r=∫ t in l..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l u, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) :
    ∀ r ∈ Ioc l u, ‖F r‖ < 1 := by
  intro r hr
  have ht := (radial_free_taylor b l u hb hl hu hlu hwidth F G hFc hGc hF hG hB r ⟨hr.1.le,hr.2⟩).2
  have hδ : 0 < r-l := sub_pos.mpr hr.1
  have hδu : r-l ≤ (1/1000 : ℝ) := by linarith [hr.2]
  have hδsq : (r-l)^2 ≤ (1/1000 : ℝ)^2 := pow_le_pow_left₀ hδ.le hδu 2
  have hprod := mul_le_mul_of_nonneg_right hb.2 (sq_nonneg (r-l))
  have hbase : 0 ≤ 1-b/2*(r-l)^2 := by nlinarith
  have heq : F r-((1-b/2*(r-l)^2 : ℝ) : ℂ)=
      F r-1+(b : ℂ)/2*((r-l : ℝ) : ℂ)^2 := by push_cast; ring
  have hn := norm_sub_norm_le (F r) (((1-b/2*(r-l)^2 : ℝ) : ℂ))
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hbase,heq] at hn
  have hbδ := mul_le_mul_of_nonneg_right hb.1 (sq_nonneg (r-l))
  nlinarith [sq_pos_of_pos hδ]

end DefocusingNLS

end OAI
