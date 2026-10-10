import OAI.Probability.PosteriorReplicas.Gaussian.GramTransform

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

def wishartMoment (ℓ m k : ℕ) : ℝ≥0∞ :=
  ∫⁻ G : Rows ℓ m, ENNReal.ofReal ((gramVolume G)⁻¹^k) ∂gaussianRows ℓ m

lemma wishartMoment_bound {ℓ m k : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) :
    wishartMoment ℓ m k ≤ gaussianMomentConstant k ^ m := by
  exact gaussian_gram_inverse_moment_centered k m hk (by simpa using hkm)

lemma wishartMoment_ne_top {ℓ m k : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) :
    wishartMoment ℓ m k ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.pow_ne_top (gaussianMomentConstant_ne_top k)) (wishartMoment_bound hk hkm)

lemma wishartMoment_pos {ℓ m k : ℕ} (hm : m ≤ ℓ) : 0 < wishartMoment ℓ m k := by
  unfold wishartMoment
  apply (lintegral_pos_iff_support (by fun_prop)).mpr
  have h : ∀ᵐ G : Rows ℓ m ∂gaussianRows ℓ m, 0 < ENNReal.ofReal ((gramVolume G)⁻¹^k) := by
    filter_upwards [ae_gaussian_columns_independent (E := Vec ℓ) m (by simpa using hm)] with G hG
    exact ENNReal.ofReal_pos.mpr (pow_pos (inv_pos.mpr (gramVolume_pos hG)) _)
  have he : (gaussianRows ℓ m) (Function.support (fun G : Rows ℓ m => ENNReal.ofReal ((gramVolume G)⁻¹^k))) = 1 := by
    apply (ae_iff_prob_eq_one (by fun_prop)).mp
    filter_upwards [h] with G hG
    exact hG.ne'
  rw [he]
  norm_num

lemma pairingColumns_inverse_moment {d ℓ m k : ℕ} {v : Rows d m} (hv : LinearIndependent ℝ v) (hm : m ≤ ℓ) :
    (∫⁻ B, (ENNReal.ofReal (gramVolume (pairingColumns v B)))⁻¹^k ∂gaussianRows d ℓ) =
      (ENNReal.ofReal (gramVolume v))⁻¹^k * wishartMoment ℓ m k := by
  have h := pairingColumns_law (ℓ := ℓ) hv
  have hi := congrArg (fun μ : Measure (Rows ℓ m) =>
    ∫⁻ G, (ENNReal.ofReal (gramVolume G))⁻¹^k ∂μ) h
  rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)] at hi
  rw [hi]
  have hd : (pairingTriangular v).det = gramVolume v := by
    rw [← Matrix.det_transpose, pairingTriangular_det]
    rfl
  simp_rw [gramVolume_columnMix,hd,abs_of_nonneg (show 0 ≤ gramVolume v from Real.sqrt_nonneg _),
    ENNReal.ofReal_mul (show 0 ≤ gramVolume v from Real.sqrt_nonneg _), ENNReal.mul_inv (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (gramVolume_pos hv))))
      (Or.inl ENNReal.ofReal_ne_top),
    mul_pow]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_gaussian_columns_independent (E := Vec ℓ) m (by simpa using hm)] with G hG
  rw [← ENNReal.ofReal_inv_of_pos (gramVolume_pos hG), ← ENNReal.ofReal_pow (inv_nonneg.mpr (gramVolume_pos hG).le)]

end PosteriorReplicas
end

end OAI
