import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousInverseWeight
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYNorm

namespace OAI

/-! # Fourier L¹ control by the exact homogeneous norm

Cauchy--Schwarz with the integrable inverse weight gives an actual L¹
Fourier representative for every vector of Y, with no quotient by polynomials.
-/

open MeasureTheory
open scoped ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem integrable_and_integral_norm_of_memLp_homogeneous (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) {f : E → ℂ}
    (hf : MemLp f 2 (homogeneousFourierMeasure a k)) :
    Integrable f ∧ (∫ ξ, ‖f ξ‖) ≤
      Real.sqrt (∫ ξ, (homogeneousFourierWeight a k ξ)⁻¹) *
        Real.sqrt (∫ ξ, ‖f ξ‖ ^ 2 ∂homogeneousFourierMeasure a k) := by
  have hn : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by
    simp only [ae_iff, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton _
  have hm := (continuous_homogeneousFourierWeight a k ha1 hk).measurable
  have hμ : volume ≪ homogeneousFourierMeasure a k := by
    apply withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    filter_upwards [hn] with ξ hξ
    exact (ENNReal.ofReal_pos.mpr (homogeneousFourierWeight_pos a k ξ hξ)).ne'
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable.mono_ac hμ
  have hfsq : Integrable (fun ξ => ‖f ξ‖ ^ 2) (homogeneousFourierMeasure a k) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hweighted : Integrable (fun ξ => homogeneousFourierWeight a k ξ * ‖f ξ‖ ^ 2) := by
    have ht := (integrable_withDensity_iff_integrable_smul'
      hm.ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hfsq
    simpa only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul] using ht
  let A : E → ℝ := fun ξ => Real.sqrt (homogeneousFourierWeight a k ξ) * ‖f ξ‖
  let B : E → ℝ := fun ξ => (Real.sqrt (homogeneousFourierWeight a k ξ))⁻¹
  have hAmeas : AEStronglyMeasurable A volume := hm.sqrt.aestronglyMeasurable.mul hfm.norm
  have hBmeas : AEStronglyMeasurable B volume := hm.sqrt.inv.aestronglyMeasurable
  have hAsq (ξ : E) : A ξ ^ 2 = homogeneousFourierWeight a k ξ * ‖f ξ‖ ^ 2 := by
    simp only [A, mul_pow, Real.sq_sqrt (homogeneousFourierWeight_nonneg a k ξ)]
  have hBsq (ξ : E) : B ξ ^ 2 = (homogeneousFourierWeight a k ξ)⁻¹ := by
    simp only [B, inv_pow, Real.sq_sqrt (homogeneousFourierWeight_nonneg a k ξ)]
  have hA : MemLp A 2 volume := (memLp_two_iff_integrable_sq hAmeas).mpr (by
    simpa only [hAsq] using hweighted)
  have hB : MemLp B 2 volume := (memLp_two_iff_integrable_sq hBmeas).mpr (by
    simpa only [hBsq] using integrable_homogeneousFourierWeight_inv a k ha ha1 hk)
  have hAB : A * B =ᵐ[volume] fun ξ => ‖f ξ‖ := by
    filter_upwards [hn] with ξ hξ
    have hpos := Real.sqrt_pos.mpr (homogeneousFourierWeight_pos a k ξ hξ)
    dsimp [A, B]
    field_simp
  have hint : Integrable (fun ξ => ‖f ξ‖) := (hA.integrable_mul hB).congr hAB
  refine ⟨(integrable_norm_iff hfm).mp hint, ?_⟩
  have hholder : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have heA : (∫ ξ, A ξ ^ 2) = ∫ ξ, ‖f ξ‖ ^ 2 ∂homogeneousFourierMeasure a k := by
    simp_rw [hAsq]
    unfold homogeneousFourierMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (homogeneousFourierWeight_nonneg a k _), smul_eq_mul]
  have heB : (∫ ξ, B ξ ^ 2) = ∫ ξ, (homogeneousFourierWeight a k ξ)⁻¹ := by
    simp_rw [hBsq]
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    (ae_of_all _ (fun ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
    (ae_of_all _ (fun ξ => inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (by simpa using hA) (by simpa using hB)
  change (∫ ξ, A ξ * B ξ) ≤ (∫ ξ, A ξ ^ 2) ^ (1 / 2 : ℝ) *
    (∫ ξ, B ξ ^ 2) ^ (1 / 2 : ℝ) at hh
  have heAB : (∫ ξ, A ξ * B ξ) = ∫ ξ, ‖f ξ‖ := integral_congr_ae hAB
  rw [heAB] at hh
  simp only [Real.rpow_two] at hh
  rw [heA, heB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  simpa only [mul_comm] using hh

end DefocusingNLS

end OAI
