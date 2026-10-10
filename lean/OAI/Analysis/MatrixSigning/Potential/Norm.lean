import Mathlib
import OAI.Analysis.MatrixSigning.Potential.MovementMat

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Movement

section
open Matrix WithLp
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

lemma norm_one_le : ‖(1 : Mat n)‖ ≤ 1 := by
  have he : (1 : Mat n) = Matrix.diagonal (fun _ => (1 : ℝ)) := by ext i j; simp [Matrix.one_apply]
  rw [he,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (by intro i; simp)

lemma inverse_geometric_bound (C : Mat n) {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (hC : ‖C‖ ≤ (1-s)^2) : ‖(1-C)⁻¹‖ ≤ s⁻¹ := by
  have hgap : s ≤ 1-‖C‖ := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs₁)]
  have hlt : ‖C‖ < 1 := by linarith
  rw [Matrix.inv_eq_left_inv (geom_series_mul_neg C hlt)]
  have hh := tsum_geometric_le_of_norm_lt_one C hlt
  have hi : (1-‖C‖)⁻¹ ≤ s⁻¹ := inv_anti₀ hs hgap
  have hone := norm_one_le (n := n)
  linarith

lemma inverse_woodbury_sqrt (A B : Mat n) (hA : A.PosSemidef)
    (hC : ‖CFC.sqrt A*B*CFC.sqrt A‖ < 1) :
    (1-A*B)⁻¹ = 1+CFC.sqrt A*(1-CFC.sqrt A*B*CFC.sqrt A)⁻¹*CFC.sqrt A*B := by
  let R := CFC.sqrt A
  let C := R*B*R
  let D := (1-C)⁻¹
  have hD : D*(1-C) = 1 := by
    unfold D
    rw [Matrix.inv_eq_left_inv (geom_series_mul_neg C hC)]
    exact geom_series_mul_neg C hC
  apply Matrix.inv_eq_left_inv
  change (1+R*D*R*B)*(1-A*B) = 1
  have he : R*R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  calc
    _ = 1-A*B+R*(D*(1-C))*R*B := by
      dsimp only [C]
      rw [← he]
      noncomm_ring
    _ = 1 := by rw [hD,mul_one,he]; abel

lemma inverse_product_bound (A B : Mat n) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : ∀ i j, 0 ≤ (A*B) i j) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    {s M : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (hM : 0 ≤ M)
    (hbound : ∀ i, ((A*B) *ᵥ z) i ≤ (1-s)^2*z i)
    (ha : ‖A‖ ≤ M) (hb : ‖B‖ ≤ M) : ‖(1-A*B)⁻¹‖ ≤ 1+M^2/s := by
  let R := CFC.sqrt A
  let C := R*B*R
  have hc : ‖C‖ ≤ (1-s)^2 := sqrt_product_norm_bound A B hA hB hAB z hz ((1-s)^2) (sq_nonneg _) hbound
  have hlt : ‖C‖ < 1 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs₁)]
  have hd : ‖(1-C)⁻¹‖ ≤ s⁻¹ := inverse_geometric_bound C hs hs₁ hc
  have hr : ‖R‖^2 = ‖A‖ := by
    rw [← (CFC.sqrt_nonneg A).posSemidef.isHermitian.isSelfAdjoint.norm_mul_self]
    exact congrArg norm (CFC.sqrt_mul_sqrt_self A hA.nonneg)
  rw [inverse_woodbury_sqrt A B hA hlt]
  calc
    ‖1+R*(1-C)⁻¹*R*B‖ ≤ ‖(1 : Mat n)‖+‖R*(1-C)⁻¹*R*B‖ := norm_add_le _ _
    _ ≤ 1+‖R‖*‖(1-C)⁻¹‖*‖R‖*‖B‖ := by
      gcongr
      · exact norm_one_le
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg R))) (norm_nonneg B))
    _ = 1+‖A‖*‖(1-C)⁻¹‖*‖B‖ := by rw [← hr]; ring
    _ ≤ 1+M*s⁻¹*M := by gcongr
    _ = 1+M^2/s := by ring

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma response_norm_bound (A B R : E →L[ℝ] E) {J M : ℝ}
    (hJ : 0 ≤ J) (hM : 0 ≤ M) (hR : ‖R‖ ≤ J) (hB : ‖B‖ ≤ M)
    (hleft : R.comp (ContinuousLinearMap.id ℝ E-B.comp A) = ContinuousLinearMap.id ℝ E)
    (F G H : E) (hF : F-B G = H) (hG : G-A F = -H) :
    ‖F‖ ≤ J*(1+M)*‖H‖ := by
  have hsolve : F = R (H-B H) := by
    have hf : F-B (A F) = H-B H := by
      have hg : G = A F-H := by rw [eq_sub_iff_add_eq]; calc
        _ = G-(G-A F) := by rw [hG]; simp
        _ = A F := by abel
      rw [hg,map_sub] at hF
      calc
        _ = (F-(B (A F)-B H))-B H := by abel
        _ = H-B H := by rw [hF]
    have hh := congrArg (fun L : E →L[ℝ] E => L F) hleft
    change R (F-B (A F)) = F at hh
    exact hh.symm.trans (congrArg R hf)
  rw [hsolve]
  calc
    ‖R (H-B H)‖ ≤ ‖R‖*‖H-B H‖ := R.le_opNorm _
    _ ≤ J*(‖H‖+‖B H‖) := mul_le_mul hR (norm_sub_le H (B H)) (norm_nonneg _) hJ
    _ ≤ J*(‖H‖+M*‖H‖) := by
      refine mul_le_mul_of_nonneg le_rfl ?_ hJ ?_
      · exact add_le_add le_rfl
          ((B.le_opNorm H).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg H)))
      · exact add_nonneg (norm_nonneg H) (mul_nonneg hM (norm_nonneg H))
    _ = J*(1+M)*‖H‖ := by ring

lemma coupled_response_energy_bound (A B R S : E →L[ℝ] E) {J M : ℝ}
    (hJ : 0 ≤ J) (hM : 0 ≤ M) (hR : ‖R‖ ≤ J) (hS : ‖S‖ ≤ J)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M)
    (hleftR : R.comp (ContinuousLinearMap.id ℝ E-B.comp A) = ContinuousLinearMap.id ℝ E)
    (hleftS : S.comp (ContinuousLinearMap.id ℝ E-A.comp B) = ContinuousLinearMap.id ℝ E)
    (F G H : E) (hF : F-B G = H) (hG : G-A F = -H) :
    ‖F‖^2+‖G‖^2 ≤ (2*J^2*(1+M)^2)*‖H‖^2 := by
  have hf := response_norm_bound A B R hJ hM hR hB hleftR F G H hF hG
  have hg := response_norm_bound B A S hJ hM hS hA hleftS G F (-H) hG (by simpa using hF)
  rw [norm_neg] at hg
  have hp : 0 ≤ J*(1+M)*‖H‖ := by positivity
  have hfs := sq_le_sq₀ (norm_nonneg F) hp |>.mpr hf
  have hgs := sq_le_sq₀ (norm_nonneg G) hp |>.mpr hg
  nlinarith

end CurrentKS.Movement

end

end OAI
