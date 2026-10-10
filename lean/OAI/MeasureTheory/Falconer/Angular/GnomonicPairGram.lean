import OAI.MeasureTheory.Falconer.Geometry.NormalizedTripleGram
import OAI.MeasureTheory.Falconer.Angular.AngularTubes

namespace OAI

/-! # Pair transversality retains the original affine separation -/

namespace Falconer
variable {n : ℕ}

noncomputable def pairGram {d : ℕ} (u v : Space d) : ℝ :=
  ‖u‖^2*‖v‖^2-(inner ℝ u v)^2

theorem pairGram_nonneg {d : ℕ} (u v : Space d) : 0 ≤ pairGram u v := by
  have hh := pow_le_pow_left₀ (abs_nonneg (inner ℝ u v))
    (abs_real_inner_le_norm u v) 2
  rw [sq_abs,mul_pow] at hh
  exact sub_nonneg.mpr hh

theorem pairGram_smul {d : ℕ} (u v : Space d) (a b : ℝ) :
    pairGram (a • u) (b • v) = (a*b)^2*pairGram u v := by
  simp only [pairGram,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right]
  ring

theorem northLift_pairGram (p q : Space n) :
    pairGram (northLift p) (northLift q) = ‖q-p‖^2+pairGram p q := by
  rw [pairGram,northLift_norm_sq,northLift_norm_sq,northLift_inner,
    norm_sub_sq_real]
  simp only [pairGram]
  rw [real_inner_comm q p]
  ring

theorem gnomonic_pairGram (p q : Space n) :
    pairGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)) =
      (‖northLift p‖⁻¹*‖northLift q‖⁻¹)^2*pairGram (northLift p) (northLift q) := by
  exact pairGram_smul _ _ _ _

theorem gnomonic_pairGram_lower {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    (1/16:ℝ)*‖q-p‖^2 ≤
      pairGram (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)) := by
  have hinv (x : Space n) (hx : ‖x‖ ≤ 1) : (1/2:ℝ) ≤ ‖northLift x‖⁻¹ := by
    rw [← one_div (‖northLift x‖)]
    apply (div_le_div_iff₀ (by norm_num) (norm_pos_iff.mpr (northLift_ne_zero x))).mpr
    simpa only [one_mul] using northLift_norm_le_two hx
  have hprod : (1/4:ℝ) ≤ ‖northLift p‖⁻¹*‖northLift q‖⁻¹ := by
    calc
      _ = (1/2:ℝ)*(1/2) := by norm_num
      _ ≤ _ := mul_le_mul (hinv p hp) (hinv q hq) (by norm_num)
        (inv_nonneg.mpr (norm_nonneg _))
  have hsq : (1/16:ℝ) ≤ (‖northLift p‖⁻¹*‖northLift q‖⁻¹)^2 := by
    nlinarith
  rw [gnomonic_pairGram,northLift_pairGram]
  exact mul_le_mul hsq (le_add_of_nonneg_right (pairGram_nonneg p q))
    (sq_nonneg _) (sq_nonneg _)

theorem gnomonic_pair_separation {p q : Space n} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖q-p‖ ≤ 4*‖perpendicularPart (gnomonicChart p : Space (n+1))
      (gnomonicChart q : Space (n+1))‖ := by
  have hh := gnomonic_pairGram_lower hp hq
  have he := norm_perpendicularPart_sq (sphere_norm (gnomonicChart p))
    (gnomonicChart q : Space (n+1))
  simp only [pairGram,sphere_norm,one_pow,one_mul] at hh
  rw [sphere_norm] at he
  nlinarith [norm_nonneg (q-p),norm_nonneg
    (perpendicularPart (gnomonicChart p : Space (n+1)) (gnomonicChart q : Space (n+1)))]

end Falconer

end OAI
