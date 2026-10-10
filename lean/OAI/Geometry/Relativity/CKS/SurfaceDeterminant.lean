import OAI.Geometry.Relativity.CKS.LocalConstraints

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma det_two_add_smul_lower (A D : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    c^2 * A.det ≤ (c • A + D).det := by
  have hAs : A 1 0 = A 0 1 := by simpa using hA.1.apply 0 1
  have hDs : D 1 0 = D 0 1 := by simpa using hD.1.apply 0 1
  have hA0 : 0 ≤ A 0 0 := hA.diag_nonneg
  have hA1 : 0 ≤ A 1 1 := hA.diag_nonneg
  have hD0 : 0 ≤ D 0 0 := hD.diag_nonneg
  have hD1 : 0 ≤ D 1 1 := hD.diag_nonneg
  have ha : (A 0 1)^2 ≤ A 0 0 * A 1 1 := by
    have h := hA.det_nonneg
    rw [Matrix.det_fin_two,hAs] at h
    nlinarith
  have hd : (D 0 1)^2 ≤ D 0 0 * D 1 1 := by
    have h := hD.det_nonneg
    rw [Matrix.det_fin_two,hDs] at h
    nlinarith
  have hp : (A 0 1 * D 0 1)^2 ≤ (A 0 0 * D 1 1) * (A 1 1 * D 0 0) := by
    have h := mul_le_mul ha hd (sq_nonneg (D 0 1)) (mul_nonneg hA0 hA1)
    nlinarith only [h]
  have hcross := two_mul_le_add_of_sq_le_mul
    (mul_nonneg hA0 hD1) (mul_nonneg hA1 hD0) hp
  have hcross' : 0 ≤ A 0 0 * D 1 1 + A 1 1 * D 0 0 - 2*A 0 1*D 0 1 := by
    linarith
  have hfinal := mul_nonneg hc hcross'
  have hdd := hD.det_nonneg
  simp only [Matrix.det_fin_two,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,hAs,hDs] at hdd ⊢
  nlinarith only [hfinal,hdd]

lemma sqrt_det_two_lower (A G : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) (hlow : (G-c•A).PosSemidef) :
    c * Real.sqrt A.det ≤ Real.sqrt G.det := by
  have h := det_two_add_smul_lower A (G-c•A) hA hlow hc
  rw [add_sub_cancel] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc] at hs
  exact hs

end CKSSurfaceVolume

end

end OAI
