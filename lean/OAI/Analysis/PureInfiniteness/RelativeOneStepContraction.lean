import OAI.Analysis.PureInfiniteness.OneStepContraction
import OAI.Analysis.PureInfiniteness.RelativeOneStep

namespace OAI

/-! Contractive one-step witnesses relative to a homomorphism. This is the
finite nonunital normalization needed for the supported two-copy map. -/

noncomputable section
open Filter Topology

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B]

lemma ApproximatelyOneStepAlong.contractive_implementations
    (φ : B →⋆ₙₐ[ℂ] D) (T : B →L[ℂ] D) (hTn : ‖T‖ ≤ 1)
    (hT : ApproximatelyOneStepAlong φ T) :
    ∀ (F : Finset B) (ε : ℝ), 0 < ε →
      ∃ d : D, ‖d‖ ≤ 1 ∧ ∀ b ∈ F, ‖T b - star d * φ b * d‖ < ε := by
  classical
  intro F ε hε
  let M : ℝ := ∑ b ∈ F, ‖b‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbM (b : B) (hb : b ∈ F) : ‖b‖ ≤ M :=
    Finset.single_le_sum (f := fun x : B => ‖x‖) (fun _ _ => norm_nonneg _) hb
  let δ : ℝ := ε / (M + 3)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨f, hf0, hfn, hfF⟩ :=
    exists_positive_contraction_sandwich_approximation F δ hδ
  obtain ⟨d, hd⟩ := hT (insert (f * f) (F.image (fun b => f * b * f))) δ hδ
  let q := φ f * d
  have hq : ‖star q * q‖ ≤ 1 + δ := by
    have he : star q * q = star d * φ (f * f) * d := by
      simp only [q, star_mul, ← map_star, map_mul, hf0.star_eq, mul_assoc]
    have happ := hd (f * f) (Finset.mem_insert_self ..)
    have hTff : ‖T (f * f)‖ ≤ 1 := by
      calc
        _ ≤ ‖T‖ * ‖f * f‖ := T.le_opNorm _
        _ ≤ 1 * (‖f‖ * ‖f‖) := by gcongr; exact norm_mul_le _ _
        _ ≤ 1 := by nlinarith [norm_nonneg f]
    rw [he]
    have htri := norm_le_norm_sub_add (star d * φ (f * f) * d) (T (f * f))
    rw [norm_sub_rev] at htri
    linarith
  let κ : ℝ := (1 + δ)⁻¹
  have hκ : 0 < κ := inv_pos.mpr (by positivity)
  have hκeq : κ * (1 + δ) = 1 := inv_mul_cancel₀ (by positivity)
  have hκ1 : κ ≤ 1 := by nlinarith
  have hκerr : 1 - κ ≤ δ := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hκ1)]
  let e : D := (Real.sqrt κ : ℂ) • q
  have hes (b : B) : star e * φ b * e = (κ : ℂ) • (star d * φ (f * b * f) * d) := by
    simp only [e, star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hκ.le]
    simp only [q, star_mul, ← map_star, map_mul, hf0.star_eq, mul_assoc]
  have hen : ‖e‖ ≤ 1 := by
    have heq : star e * e = (κ : ℂ) • (star q * q) := by
      simp only [e, star_smul, Complex.star_def,
        Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hκ.le]
    have hnorm : ‖star e * e‖ ≤ 1 := by
      rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
      exact (mul_le_mul_of_nonneg_left hq hκ.le).trans_eq hκeq
    rw [CStarRing.norm_star_mul_self] at hnorm
    nlinarith [norm_nonneg e]
  refine ⟨e, hen, fun b hb => ?_⟩
  have hinner : ‖T (f * b * f) - star d * φ (f * b * f) * d‖ < δ :=
    hd _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  have hcut : ‖T b - T (f * b * f)‖ < δ := by
    rw [← map_sub]
    calc
      _ ≤ ‖T‖ * ‖b - f * b * f‖ := T.le_opNorm _
      _ ≤ ‖b - f * b * f‖ := by nlinarith [norm_nonneg (b - f * b * f)]
      _ < δ := by rw [norm_sub_rev]; exact hfF b hb
  have hTb : ‖T b‖ ≤ M := by
    calc
      _ ≤ ‖T‖ * ‖b‖ := T.le_opNorm _
      _ ≤ ‖b‖ := by nlinarith [norm_nonneg b]
      _ ≤ M := hbM b hb
  have hsplit : T b - star e * φ b * e =
      ((1 - κ : ℝ) : ℂ) • T b +
        (κ : ℂ) • (T b - T (f * b * f)) +
        (κ : ℂ) • (T (f * b * f) - star d * φ (f * b * f) * d) := by
    rw [hes]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖((1 - κ : ℝ) : ℂ) • T b‖ +
        ‖(κ : ℂ) • (T b - T (f * b * f))‖ +
        ‖(κ : ℂ) • (T (f * b * f) - star d * φ (f * b * f) * d)‖ := norm_add₃_le
    _ = (1 - κ) * ‖T b‖ + κ * ‖T b - T (f * b * f)‖ +
        κ * ‖T (f * b * f) - star d * φ (f * b * f) * d‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hκ1), abs_of_pos hκ]
    _ ≤ δ * M + δ + δ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul hκerr hTb (norm_nonneg _) hδ.le
        · simpa only [one_mul] using
            mul_le_mul hκ1 hcut.le (norm_nonneg _) zero_le_one
      · simpa only [one_mul] using
          mul_le_mul hκ1 hinner.le (norm_nonneg _) zero_le_one
    _ < ε := by
      have heq : δ * (M + 3) = ε := div_mul_cancel₀ ε (by positivity)
      nlinarith

end WeakPureInfiniteness

end

end OAI
