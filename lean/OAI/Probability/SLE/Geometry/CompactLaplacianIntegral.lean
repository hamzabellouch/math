import OAI.Probability.SLE.Geometry.CompactDerivativeIntegral
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace OAI

/-! A compactly supported smooth planar test has zero total Laplacian.
This lets its integral over a conformal image be evaluated on the
compact omitted set instead. -/
noncomputable section
open Set Filter Metric Function MeasureTheory InnerProductSpace
open scoped Topology Laplacian

namespace SLEExactGauge

lemma integral_complex_imag_partial_eq_zero {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∫ z, fderiv ℝ f z Complex.I=0 := by
  let D (z : ℂ) := fderiv ℝ f z Complex.I
  have hD : Continuous D := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDi : Integrable D := hD.integrable_of_hasCompactSupport (hs.fderiv_apply ℝ Complex.I)
  have hline (x : ℝ) : ∫ y : ℝ, D ((x:ℂ)+(y:ℂ)*Complex.I)=0 := by
    let L (y : ℝ) := (x:ℂ)+(y:ℂ)*Complex.I
    have hLc : ContDiff ℝ 1 L := contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    have hLi : Isometry L := by
      apply isometry_iff_dist_eq.mpr
      intro y y'
      rw [dist_eq_norm,show L y-L y'=((y-y':ℝ):ℂ)*Complex.I by dsimp [L]; push_cast; ring]
      simp only [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,dist_eq_norm]
    have hcs : HasCompactSupport (f ∘ L) := hs.comp_isClosedEmbedding hLi.isClosedEmbedding
    have he (y : ℝ) : deriv (f ∘ L) y=D (L y) := by
      have hd := (hf.differentiable (by norm_num) (L y)).hasFDerivAt.comp_hasDerivAt y
        (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x:ℂ))
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using hd.deriv
    simpa only [he] using integral_deriv_compact_eq_zero (hf.comp hLc) hcs
  let e := Complex.measurableEquivRealProd.symm
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hprod : Integrable (fun p : ℝ × ℝ => D (e p)) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hDi
  rw [←hp.integral_comp e.measurableEmbedding]
  change (∫ p : ℝ × ℝ, D (e p))=0
  rw [Measure.volume_eq_prod] at hprod ⊢
  rw [integral_prod _ hprod]
  have he (x : ℝ) : (∫ y : ℝ, D (e (x,y)))=0 := by
    have heq (x y : ℝ) : e (x,y)=(x:ℂ)+(y:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [e,Complex.measurableEquivRealProd_symm_apply]
    simpa only [heq] using hline x
  simp only [he,integral_zero]

lemma integral_laplacian_compact_eq_zero {f : ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) : ∫ z, (Δ f) z=0 := by
  let A (z : ℂ) := fderiv ℝ f z 1
  let B (z : ℂ) := fderiv ℝ f z Complex.I
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hA : ContDiff ℝ 1 A := hDf.clm_apply contDiff_const
  have hB : ContDiff ℝ 1 B := hDf.clm_apply contDiff_const
  have hsA : HasCompactSupport A := hs.fderiv_apply ℝ 1
  have hsB : HasCompactSupport B := hs.fderiv_apply ℝ Complex.I
  have hAA (z : ℂ) : fderiv ℝ A z 1=fderiv ℝ (fderiv ℝ f) z 1 1 := by
    have h := (hDf.differentiable (by norm_num) z).hasFDerivAt.clm_apply
      (hasFDerivAt_const (1:ℂ) z)
    rw [h.fderiv]
    simp
  have hBB (z : ℂ) : fderiv ℝ B z Complex.I=fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
    have h := (hDf.differentiable (by norm_num) z).hasFDerivAt.clm_apply
      (hasFDerivAt_const Complex.I z)
    rw [h.fderiv]
    simp
  have hpoint (z : ℂ) : (Δ f) z=fderiv ℝ A z 1+fderiv ℝ B z Complex.I := by
    rw [hAA,hBB,laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
  simp_rw [hpoint]
  rw [integral_add
    (((hA.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport (hsA.fderiv_apply ℝ 1))
    (((hB.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport (hsB.fderiv_apply ℝ Complex.I)),
    integral_complex_real_partial_eq_zero hA hsA,integral_complex_imag_partial_eq_zero hB hsB,add_zero]

end SLEExactGauge

end

end OAI
