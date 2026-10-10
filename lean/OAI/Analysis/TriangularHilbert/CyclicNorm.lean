import OAI.Analysis.TriangularHilbert.CyclicHomogeneity

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
open scoped ENNReal NNReal
noncomputable section

def mainConstant : ℝ≥0 := ⟨(2*momentConstant)^((2:ℝ)/3),Real.rpow_nonneg (mul_nonneg (by norm_num) momentConstant_pos.le) _⟩

lemma coe_mainConstant : (mainConstant : ℝ≥0∞) = ENNReal.ofReal (2*momentConstant)^((2:ℝ)/3) := by
  rw [ENNReal.coe_nnreal_eq]
  exact (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by norm_num) momentConstant_pos.le) (by norm_num)).symm

lemma ofReal_integral_cube (B : Plane → ℂ) (hB : MemLp B 3 volume) :
    ENNReal.ofReal (∫ z : Plane, ‖B z‖^3) = eLpNorm B 3 volume ^ (3:ℕ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hB.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0))
    (Eventually.of_forall (fun z => pow_nonneg (norm_nonneg (B z)) 3))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  exact lintegral_enorm_cube B volume hB.aestronglyMeasurable

lemma integral_cube_eq_one (B : Plane → ℂ) (hB : MemLp B 3 volume) (hn : eLpNorm B 3 volume = 1) :
    (∫ z : Plane, ‖B z‖^3) = 1 := by
  have h := congrArg ENNReal.toReal (ofReal_integral_cube B hB)
  simpa only [hn,one_pow,ENNReal.toReal_one,
    ENNReal.toReal_ofReal (integral_nonneg (fun z => pow_nonneg (norm_nonneg (B z)) 3))] using h

lemma cyclicNorm_le_unit (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    (hnB : eLpNorm B 3 volume = 1) (hnC : eLpNorm C 3 volume = 1) :
    cyclicNorm B C ≤ (mainConstant : ℝ≥0∞) := by
  rw [cyclicNorm,coe_mainConstant]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have h := lintegral_cyclicMax_moment_le B C hB hC
  rw [integral_cube_eq_one B hB hnB,integral_cube_eq_one C hC hnC] at h
  simpa only [show momentConstant*((1:ℝ)+1) = 2*momentConstant by ring] using h

lemma cyclicNorm_le (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    cyclicNorm B C ≤ (mainConstant : ℝ≥0∞)*eLpNorm B 3 volume*eLpNorm C 3 volume := by
  by_cases hb0 : eLpNorm B 3 volume = 0
  · have hb := (eLpNorm_eq_zero_iff (by norm_num)).mp hb0
    rw [cyclicNorm_congr_ae hb (EventuallyEq.refl _ _),cyclicNorm_zero_left]
    exact bot_le
  by_cases hc0 : eLpNorm C 3 volume = 0
  · have hc := (eLpNorm_eq_zero_iff (by norm_num)).mp hc0
    rw [cyclicNorm_congr_ae (EventuallyEq.refl _ _) hc,cyclicNorm_zero_right]
    exact bot_le
  let u : ℂ := (eLpNorm B 3 volume).toReal
  let v : ℂ := (eLpNorm C 3 volume).toReal
  have hu : ‖u‖ₑ = eLpNorm B 3 volume := by
    rw [← ofReal_norm]
    simp only [u,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hB.ne]
  have hv : ‖v‖ₑ = eLpNorm C 3 volume := by
    rw [← ofReal_norm]
    simp only [v,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hC.ne]
  have hu0 : u ≠ 0 := by
    intro he
    exact hb0 (by simpa only [he,enorm_zero] using hu.symm)
  have hv0 : v ≠ 0 := by
    intro he
    exact hc0 (by simpa only [he,enorm_zero] using hv.symm)
  have hiB : MemLp (u⁻¹ • B) 3 volume := hB.const_smul _
  have hiC : MemLp (v⁻¹ • C) 3 volume := hC.const_smul _
  have hnB : eLpNorm (u⁻¹ • B) 3 volume = 1 := by
    rw [eLpNorm_const_smul,enorm_inv hu0,hu,ENNReal.inv_mul_cancel hb0 hB.ne]
  have hnC : eLpNorm (v⁻¹ • C) 3 volume = 1 := by
    rw [eLpNorm_const_smul,enorm_inv hv0,hv,ENNReal.inv_mul_cancel hc0 hC.ne]
  calc
    cyclicNorm B C = cyclicNorm (u • (u⁻¹ • B)) (v • (v⁻¹ • C)) := by
      rw [smul_smul,smul_smul,mul_inv_cancel₀ hu0,mul_inv_cancel₀ hv0,one_smul,one_smul]
    _ = (‖u‖ₑ*‖v‖ₑ)*cyclicNorm (u⁻¹ • B) (v⁻¹ • C) := cyclicNorm_smul _ _ _ _
    _ ≤ (‖u‖ₑ*‖v‖ₑ)*(mainConstant : ℝ≥0∞) := by
      gcongr
      exact cyclicNorm_le_unit _ _ hiB hiC hnB hnC
    _ = (mainConstant : ℝ≥0∞)*eLpNorm B 3 volume*eLpNorm C 3 volume := by
      rw [hu,hv]
      ac_rfl
end
end TriangularHilbert
end

end OAI
