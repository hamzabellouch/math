import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Norm

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Movement

section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma inverse_product_left (A B : Mat n) (hA : A.PosSemidef)
    (hC : ‖CFC.sqrt A*B*CFC.sqrt A‖ < 1) : (1-A*B)⁻¹*(1-A*B) = 1 := by
  let R := CFC.sqrt A
  let C := R*B*R
  have hD : (1-C)⁻¹*(1-C) = 1 := by
    rw [Matrix.inv_eq_left_inv (geom_series_mul_neg C hC)]
    exact geom_series_mul_neg C hC
  have he : R*R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  rw [inverse_woodbury_sqrt A B hA hC]
  change (1+R*(1-C)⁻¹*R*B)*(1-A*B) = 1
  calc
    _ = 1-A*B+R*((1-C)⁻¹*(1-C))*R*B := by
      dsimp only [C]
      rw [← he]
      noncomm_ring
    _ = 1 := by rw [hD,mul_one,he]; abel

lemma matrix_coupled_response_bound (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAnon : ∀ i j, 0 ≤ A i j) (hBnon : ∀ i j, 0 ≤ B i j)
    (z w : Fin n → ℝ) (hz : ∀ i, 0 < z i) (hw : ∀ i, 0 < w i)
    {s M : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hM : 0 ≤ M)
    (hAw : ∀ i, (A *ᵥ w) i ≤ (1-s)*z i) (hBz : ∀ i, (B *ᵥ z) i ≤ (1-s)*w i)
    (ha : ‖A‖ ≤ M) (hb : ‖B‖ ≤ M)
    (F G H : EuclideanSpace ℝ (Fin n))
    (hF : F-B.toEuclideanLin G = H) (hG : G-A.toEuclideanLin F = -H) :
    ‖F‖^2+‖G‖^2 ≤ (2*(1+M^2/s)^2*(1+M)^2)*‖H‖^2 := by
  have hnAB : ∀ i j, 0 ≤ (A*B) i j := by
    intro i j
    change 0 ≤ ∑ k, A i k*B k j
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hAnon i k) (hBnon k j)
  have hnBA : ∀ i j, 0 ≤ (B*A) i j := by
    intro i j
    change 0 ≤ ∑ k, B i k*A k j
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hBnon i k) (hAnon k j)
  have hprod := product_weighted_bound A B hAnon z w (1-s) (sub_nonneg.mpr hs₁) hAw hBz
  have hprod' := product_weighted_bound B A hBnon w z (1-s) (sub_nonneg.mpr hs₁) hBz hAw
  have hinv := inverse_product_bound A B hA hB hnAB z hz hs hs₁ hM hprod ha hb
  have hinv' := inverse_product_bound B A hB hA hnBA w hw hs hs₁ hM hprod' hb ha
  have hlt : (1-s)^2 < 1 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs₁)]
  have hleft := inverse_product_left A B hA ((sqrt_product_norm_bound A B hA hB hnAB z hz _
    (sq_nonneg _) hprod).trans_lt hlt)
  have hleft' := inverse_product_left B A hB ((sqrt_product_norm_bound B A hB hA hnBA w hw _
    (sq_nonneg _) hprod').trans_lt hlt)
  apply coupled_response_energy_bound (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) ((1-B*A)⁻¹)) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) ((1-A*B)⁻¹))
    (by positivity) hM _ _ ha hb _ _ F G H hF hG
  · exact hinv'
  · exact hinv
  · have hh := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hleft'
    simp only [map_mul,map_sub,map_one,ContinuousLinearMap.mul_def] at hh
    exact hh
  · have hh := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) hleft
    simp only [map_mul,map_sub,map_one,ContinuousLinearMap.mul_def] at hh
    exact hh

end

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}
lemma psd_norm_le_trace (A : Mat n) (hA : A.PosSemidef) : ‖A‖ ≤ A.trace := by
  have ht : 0 ≤ A.trace := Finset.sum_nonneg fun i _ => hA.diag_nonneg
  have heig : ∀ i, ‖hA.isHermitian.eigenvalues i‖ ≤ A.trace := by
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hA.eigenvalues_nonneg i),hA.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  calc
    ‖A‖ = ‖(Matrix.diagonal (hA.isHermitian.eigenvalues) : Mat n)‖ := by
      conv_lhs => rw [hA.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply]
      rw [mul_assoc,CStarRing.norm_coe_unitary_mul,← Unitary.coe_star,CStarRing.norm_mul_coe_unitary]
      rfl
    _ ≤ A.trace := by rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg ht).mpr heig
end CurrentKS.Movement

end

end OAI
