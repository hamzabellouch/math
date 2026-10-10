import OAI.Analysis.FreeEntropy.BilinearNet

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set Metric
namespace FiniteEntropySeparation
 def gueMatrix {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  ((Real.sqrt d : ℂ)⁻¹) • coordinateMatrix x i
 theorem coordinateMatrix_norm_tail {n d : ℕ} (i : Fin n) {u : ℝ} (hu : 0 ≤ u) :
    (productGaussian (MatrixIndex n d)).real {x | 2*u < matrixOpNorm (coordinateMatrix x i)} ≤
      4*9^(4*d)*Real.exp (-u^2/8) := by
  classical
  obtain ⟨s,hs,hcov,hcard⟩ := sphere_finite_net (E := EuclideanSpace ℂ (Fin d))
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2*d := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace_fin]
  rw [hdim] at hcard
  let E : EuclideanSpace ℂ (Fin d) × EuclideanSpace ℂ (Fin d) → Set (MatrixIndex n d → ℝ) :=
    fun q => {x | u ≤ ‖matrixBilinear q.1 q.2 (coordinateMatrix x i)‖}
  have hsub : {x | 2*u < matrixOpNorm (coordinateMatrix x i)} ⊆ ⋃ q ∈ s ×ˢ s, E q := by
    intro x hx
    by_contra hh
    have hall : ∀ v ∈ s, ∀ w ∈ s, ‖matrixBilinear v w (coordinateMatrix x i)‖ ≤ u := by
      intro v hv w hw
      have hn : x ∉ E (v,w) := fun h => hh (mem_iUnion₂.mpr ⟨(v,w), mem_product.mpr ⟨hv,hw⟩, h⟩)
      exact (not_le.mp hn).le
    have hb := bilinear_net_bound (matrixOperator (coordinateMatrix x i)) s hs hcov hu hall
    exact (not_lt_of_ge hb) hx
  calc
    _ ≤ (productGaussian (MatrixIndex n d)).real (⋃ q ∈ s ×ˢ s, E q) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ q ∈ s ×ˢ s, (productGaussian (MatrixIndex n d)).real (E q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ s ×ˢ s, 4*Real.exp (-u^2/8) := by
      apply sum_le_sum
      intro q hq
      exact matrixBilinear_gaussian_tail i q.1 q.2 (hs _ (mem_product.mp hq).1) (hs _ (mem_product.mp hq).2) hu
    _ = (s.card:ℝ)^2*(4*Real.exp (-u^2/8)) := by simp [sq]
    _ ≤ (9^(2*d))^2*(4*Real.exp (-u^2/8)) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (by positivity)
    _ = _ := by rw [← pow_mul, show 2*d*2=4*d by omega]; ring
 theorem gueMatrix_norm {n d : ℕ} (x : MatrixIndex n d → ℝ) (i : Fin n) :
    matrixOpNorm (gueMatrix x i) = (Real.sqrt d)⁻¹ * matrixOpNorm (coordinateMatrix x i) := by
  rw [gueMatrix, matrixOpNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
 theorem gueMatrix_norm_tail {n d : ℕ} (hd : 0 < d) (i : Fin n) {L : ℝ} (hL : 0 ≤ L) :
    (productGaussian (MatrixIndex n d)).real {x | L < matrixOpNorm (gueMatrix x i)} ≤
      4*9^(4*d)*Real.exp (-((d:ℝ)*L^2)/32) := by
  have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd'
  have he : {x : MatrixIndex n d → ℝ | L < matrixOpNorm (gueMatrix x i)} =
      {x | 2*(L*Real.sqrt d/2) < matrixOpNorm (coordinateMatrix x i)} := by
    ext x
    simp only [mem_ofPred_eq, gueMatrix_norm, ← div_eq_inv_mul, lt_div_iff₀ hs]
    ring_nf
  rw [he]
  convert coordinateMatrix_norm_tail i (u := L*Real.sqrt d/2) (by positivity) using 1
  congr 2
  rw [div_pow, mul_pow, Real.sq_sqrt hd'.le]
  ring
end FiniteEntropySeparation

end

end OAI
