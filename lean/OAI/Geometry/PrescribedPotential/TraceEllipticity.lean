import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixFrameNormalization

namespace OAI

/-! Trace Ellipticity. -/

section

 
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma eig_upper_psd {M : Matrix (Fin n) (Fin n) ℂ} (hh : M.IsHermitian)
    (C : ℝ) (he : ∀ i, hh.eigenvalues i ≤ C) : (((C:ℂ) • 1)-M).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => ((C-hh.eigenvalues i:ℝ):ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0:ℂ) ≤ ((C-hh.eigenvalues i:ℝ):ℂ)
      exact_mod_cast sub_nonneg.mpr (he i))
  have hu := hd.mul_mul_conjTranspose_same (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hD : Matrix.diagonal (fun i => ((C-hh.eigenvalues i:ℝ):ℂ)) =
      (C:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-Matrix.diagonal (fun i => (hh.eigenvalues i:ℂ)) := by
    simp only [Complex.ofReal_sub,Matrix.diagonal_sub,Matrix.smul_one_eq_diagonal]
  rw [hD,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul] at hu
  have hunit : (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)*
      (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := Unitary.coe_mul_star_self _
  rw [hunit] at hu
  have hs := hh.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply,Function.comp_def] at hs
  exact hs ▸ hu

lemma trace_upper_psd {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) :
    (((M.trace.re:ℂ) • 1)-M).PosSemidef := by
  apply eig_upper_psd hM.isHermitian
  intro i
  rw [hM.isHermitian.trace_eq_sum_eigenvalues,Complex.re_sum]
  exact Finset.single_le_sum (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma inverse_trace_lower_psd {M G : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosDef) (hG : G.PosDef) {R : ℝ} (hR : (M⁻¹*G).trace.re ≤ R) :
    (((R:ℂ) • M)-G).PosSemidef := by
  obtain ⟨B,hB,hBM⟩ := whitening M hM
  let N := Bᴴ*G*B
  have hN : N.PosDef := hG.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hB)
  have htr : N.trace.re = (M⁻¹*G).trace.re := by
    have he := matrix_inverse_trace_congruence B M G hB
    rw [hBM,inv_one,one_mul] at he
    exact congrArg Complex.re he
  have hn := trace_upper_psd hN.posSemidef
  have hd : (((R-N.trace.re:ℝ):ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.PosSemidef.smul Matrix.PosSemidef.one (by exact_mod_cast sub_nonneg.mpr (htr ▸ hR))
  have hh := hn.add hd
  have he : (((N.trace.re:ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))-N)+
      ((R-N.trace.re:ℝ):ℂ) • 1 = (R:ℂ) • 1-N := by
    rw [Complex.ofReal_sub,sub_smul]
    abel
  rw [he] at hh
  have hp : (Bᴴ*((R:ℂ) • M-G)*B).PosSemidef := by
    simpa only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hBM] using hh
  exact (hB.posSemidef_star_left_conjugate_iff).mp hp

lemma inverse_trace_eigenvalues {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) :
    M⁻¹.trace.re = ∑ i, (hM.isHermitian.eigenvalues i)⁻¹ := by
  let U := hM.isHermitian.eigenvectorUnitary
  have hs := hM.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply,Function.comp_def] at hs
  change M = (U : Matrix (Fin n) (Fin n) ℂ) *
    Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i:ℂ)) *
    (U : Matrix (Fin n) (Fin n) ℂ)ᴴ at hs
  have hu : (U : Matrix (Fin n) (Fin n) ℂ)⁻¹ = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ :=
    Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self U)
  have hv : ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ)⁻¹ = (U : Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_mul_star_self U)
  have hid : (Matrix.diagonal (fun i => (hM.isHermitian.eigenvalues i:ℂ)))⁻¹ =
      Matrix.diagonal (fun i => ((hM.isHermitian.eigenvalues i:ℂ))⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    have he : (fun i => (hM.isHermitian.eigenvalues i:ℂ)⁻¹ * (hM.isHermitian.eigenvalues i:ℂ)) = fun _ => 1 := by
      funext i
      exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hM.eigenvalues_pos i).ne')
    rw [he, Matrix.diagonal_one]
  have hi : M⁻¹ = (U : Matrix (Fin n) (Fin n) ℂ)*
      Matrix.diagonal (fun i => (((hM.isHermitian.eigenvalues i)⁻¹:ℝ):ℂ)) *
      (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    conv_lhs => rw [hs]
    simp only [Matrix.mul_inv_rev, hu, hv, hid, Matrix.mul_assoc]
    simp only [Complex.ofReal_inv]
  have huu : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [hi, Matrix.trace_mul_cycle, huu, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum]
  rfl

lemma inverse_trace_det_upper {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef)
    {R D : ℝ} (_hR0 : 0 ≤ R) (hR : M⁻¹.trace.re ≤ R) (hD : M.det.re ≤ D) :
    ((((D * R^(n-1):ℝ):ℂ) • 1)-M).PosSemidef := by
  apply eig_upper_psd hM.isHermitian
  intro i
  let ell := hM.isHermitian.eigenvalues
  have hp : ∀ j, 0 < ell j := hM.eigenvalues_pos
  have hb : ∀ j, (ell j)⁻¹ ≤ R := by
    intro j
    apply le_trans _ hR
    rw [inverse_trace_eigenvalues hM]
    exact Finset.single_le_sum (fun k _ => inv_nonneg.mpr (hp k).le) (Finset.mem_univ j)
  have hprod : (∏ j ∈ Finset.univ.erase i, (ell j)⁻¹) ≤ R^(n-1) := by
    have hh := Finset.prod_le_prod₀ (s := Finset.univ.erase i)
      (fun j _ => inv_nonneg.mpr (hp j).le) (fun j _ => hb j)
    simpa only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin] using hh
  have hdet : M.det.re = ∏ j, ell j := by
    rw [hM.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    rfl
  have he : ell i = M.det.re * ∏ j ∈ Finset.univ.erase i, (ell j)⁻¹ := by
    rw [hdet,← Finset.mul_prod_erase Finset.univ ell (Finset.mem_univ i),
      Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀, mul_one]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => (hp j).ne')
  change ell i ≤ _
  rw [he]
  exact mul_le_mul hD hprod
    (Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (hp j).le))
    (le_trans (Complex.nonneg_iff.mp hM.det_pos.le).1 hD)

lemma det_ratio_whitening {M G B : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosDef) (hG : G.PosDef) (hB : IsUnit B) (hBG : Bᴴ*G*B = 1) :
    (Bᴴ*M*B).det.re = M.det.re/G.det.re := by
  have hN := hM.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hB)
  have he : (Bᴴ*M*B).det * G.det = M.det := by
    have hh := congrArg Matrix.det hBG
    simp only [Matrix.det_mul, Matrix.det_one] at hh ⊢
    calc
      Bᴴ.det * M.det * B.det * G.det = M.det * (Bᴴ.det * G.det * B.det) := by ring
      _ = M.det := by rw [hh,mul_one]
  have hr : (Bᴴ*M*B).det.re * G.det.re = M.det.re := by
    have hh := congrArg Complex.re he
    rw [Complex.mul_re, ← (Complex.pos_iff.mp hN.det_pos).2,
      zero_mul,sub_zero] at hh
    exact hh
  exact (eq_div_iff (ne_of_gt (Complex.pos_iff.mp hG.det_pos).1)).mpr hr

lemma inverse_trace_relative_upper {M G : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosDef) (hG : G.PosDef) {R D : ℝ}
    (hR0 : 0 ≤ R) (hR : (M⁻¹*G).trace.re ≤ R) (hD : M.det.re/G.det.re ≤ D) :
    ((((D*R^(n-1):ℝ):ℂ) • G)-M).PosSemidef := by
  obtain ⟨B,hB,hBG⟩ := whitening G hG
  let N := Bᴴ*M*B
  have hN : N.PosDef := hM.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hB)
  have htr : N⁻¹.trace.re = (M⁻¹*G).trace.re := by
    have he := matrix_inverse_trace_congruence B M G hB
    rw [hBG,mul_one] at he
    exact congrArg Complex.re he
  have hd : N.det.re ≤ D := (det_ratio_whitening hM hG hB hBG).trans_le hD
  have hh := inverse_trace_det_upper hN hR0 (htr ▸ hR) hd
  have he : (Bᴴ*((((D*R^(n-1):ℝ):ℂ) • G)-M)*B).PosSemidef := by
    simpa only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,hBG] using hh
  exact hB.posSemidef_star_left_conjugate_iff.mp he
end KaehlerCalculus

end
end

end OAI
