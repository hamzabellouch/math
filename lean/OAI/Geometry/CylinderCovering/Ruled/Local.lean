import OAI.Geometry.CylinderCovering.Ruled.LogarithmicLocalDefinitions
import OAI.Geometry.CylinderCovering.Ruled.LocalEndpoint
import OAI.Geometry.CylinderCovering.Ruled.Remainder

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering.ProductLocal
open RuledApproximation

lemma affineCell_dilation (p : Plane) (t m : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane) (S : Set (ℝ × ℝ)) :
    affineCell p t L (ProductCells.dilation m '' S) =
      affineCell p (m*t) L S := by
  simp only [affineCell, image_image]
  congr 1
  funext s
  have hd : ProductCells.dilation m s = m • s := by
    ext <;> rfl
  rw [hd, map_smul, smul_smul, mul_comm t m]

lemma affine_logarithmicCell (p : Plane) (t : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane) {m : ℝ} (hm : 0 < m) :
    affineCell p t L (ProductCells.logarithmicCell m) =
      affineCell p (m*t) L (ProductCells.parameterCell (1/m^2)) := by
  rw [ProductCells.logarithmicCell_eq_dilation m hm, affineCell_dilation]

lemma affine_logarithmicIntercept (p : Plane) (t gamma : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane) {m : ℝ} (hm : 0 < m) :
    affineCell p t L (ProductCells.logarithmicIntercept m gamma) =
      affineCell p (m*t) L (ProductCells.interceptCell (1/m^2) gamma) := by
  rw [ProductCells.logarithmicIntercept_eq_dilation m gamma hm, affineCell_dilation]

lemma logarithmic_projectedCylinder_eq (p g : Plane) (t gamma h : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane) {m : ℝ} (hm : 0 < m) :
    projectedCylinder h g (affineCell p t L (ProductCells.logarithmicIntercept m gamma)) =
      projectedCylinder h g (affineCell p (m*t) L (ProductCells.interceptCell (1/m^2) gamma)) := by
  rw [affine_logarithmicIntercept p t gamma L hm]

theorem logarithmic_local_proof : LogarithmicLocalStatement := by
  intro D v h M hD hDne hh hM hv hhyper eta m gamma heta hm hgamma hpad hratio
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  have htau : 0 < 1/m^2 := by positivity
  have htau1 : 1/m^2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos hm0)).mpr
    nlinarith
  obtain ⟨rho0, hrho0, hlocal⟩ :=
    local_proof D v h M hD hDne hh hM hv hhyper eta (1/m^2) gamma
      heta htau htau1 hgamma hpad hratio
  refine ⟨rho0/m, div_pos hrho0 hm0, ?_⟩
  intro p hp lam L hL hlam0 hlam1 t ht ht0 hGD
  have hmt : m*t < rho0 := by
    have := (lt_div_iff₀ hm0).mp ht0
    simpa only [mul_comm t m] using this
  have hG : affineCell p (m*t) L (ProductCells.parameterCell (1/m^2)) ⊆ D := by
    rwa [affine_logarithmicCell p t L hm0] at hGD
  obtain ⟨C, haxis, hcarrier, hopen, hcover, hcost⟩ :=
    hlocal p hp lam L hL hlam0 hlam1 (m*t) (mul_pos hm0 ht) hmt hG
  refine ⟨C, haxis, ?_, hopen, ?_, ?_⟩
  · simpa only [affine_logarithmicIntercept p t gamma L hm0] using hcarrier
  · simpa only [affine_logarithmicCell p t L hm0] using hcover
  · simpa only [affine_logarithmicCell p t L hm0] using hcost

theorem logarithmic_source_local : SourceLogarithmicLocalStatement := by
  intro X k D v hX hk hD hDne hv hH eta heta
  obtain ⟨U, hU, hDU, hv1⟩ := hv.smoothNear
  have hw : SmoothNear 1 D (fun q => k • v q) :=
    ⟨U, hU, hDU, hv1.const_smul k⟩
  have hf (p : Plane) (hp : p ∈ D) :
      fderiv ℝ (fun q => k • v q) p = k • fderiv ℝ v p :=
    (((hv1.contDiffAt (hU.mem_nhds (hDU hp))).differentiableAt
      (by norm_num)).hasFDerivAt.const_smul k).fderiv
  have hhyp : ∀ p ∈ D, HyperbolicAt X (fun q => k • v q) p := by
    intro p hp
    obtain ⟨htr, hdet, hsmall⟩ := hH p hp
    obtain ⟨hplus, hminus⟩ :=
      plane_hyperbolic_eigenvalues (fderiv ℝ v p).toLinearMap htr hdet
    have hlam : 0 < Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) :=
      Real.sqrt_pos.mpr (neg_pos.mpr hdet)
    refine ⟨k*Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap),
      by positivity, by nlinarith, ?_, ?_⟩
    · rw [hf p hp]
      exact eigenvalue_smul _ hplus k
    · rw [hf p hp]
      change Module.End.HasEigenvalue (k • (fderiv ℝ v p).toLinearMap) (-(k*_))
      rw [← mul_neg]
      exact eigenvalue_smul _ hminus k
  obtain ⟨m, hm, gamma, hgamma, hpad, hratio⟩ :=
    ProductCells.exists_logarithmic_parameters heta
  obtain ⟨t0, ht0, hlocal⟩ := logarithmic_local_proof D (fun q => k • v q) 1 X
    hD hDne (by norm_num) hX hw hhyp eta m gamma heta hm hgamma hpad hratio.le
  refine ⟨m, hm, gamma, hgamma, hpad, hratio, t0, ht0, ?_⟩
  intro p hp lam L hlam hL t ht htt0 hGD
  have heig : Module.End.HasEigenvalue (fderiv ℝ v p).toLinearMap lam := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := L (1,0))
    refine ⟨Module.End.mem_eigenspace_iff.mpr hL.2.2.1, ?_⟩
    intro hz
    have hn := hL.1
    rw [hz, norm_zero] at hn
    norm_num at hn
  have heq := positive_eigenvalue_eq_sqrt (fderiv ℝ v p)
    (hH p hp).1 (hH p hp).2.1 hlam heig
  have hsmall : X*(k*lam) < 1 := by
    rw [heq]
    nlinarith [(hH p hp).2.2]
  have hscaled : IsUnitEigenframe (fderiv ℝ (fun q => k • v q) p) (k*lam) L := by
    rw [hf p hp]
    refine ⟨hL.1, hL.2.1, ?_, ?_⟩
    · change k • (fderiv ℝ v p) (L (1,0)) = (k*lam) • L (1,0)
      rw [hL.2.2.1, smul_smul]
    · change k • (fderiv ℝ v p) (L (0,1)) = (-(k*lam)) • L (0,1)
      rw [hL.2.2.2, smul_smul, mul_neg]
  obtain ⟨C, haxis, hcarrier, hopen, hcover, hcost⟩ :=
    hlocal p hp (k*lam) L hscaled (by positivity) hsmall t ht htt0 hGD
  refine ⟨C, ?_, hcarrier, hopen, hcover, ?_⟩
  · simpa only [PiLp.smul_apply, smul_eq_mul, one_mul] using haxis
  · have hweight (q : Plane) : physicalWeight 1 (k • v q) =
        1 / Real.sqrt (1+k^2*‖v q‖^2) := by
      rw [physicalWeight_one, weight, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simpa only [one_mul, hweight] using hcost

theorem complete_local_proof : CompleteLocalStatement :=
  ⟨ProductCells.geometry_proof, local_proof,
    logarithmic_local_proof, logarithmic_source_local, logarithmic_remainder_proof⟩

end CylinderCovering.ProductLocal

end

end OAI
