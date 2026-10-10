import Mathlib

namespace OAI

/-! Compactly supported derivative integrals used in the exterior
area calculation. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma integral_deriv_compact_eq_zero {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) : ∫ x, deriv f x=0 := by
  have hi : Integrable (deriv f) := (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hs.deriv
  rw [←integral_add_compl measurableSet_Iic hi,compl_Iic,
    hs.integral_Iic_deriv_eq hf 0,hs.integral_Ioi_deriv_eq hf 0]
  ring

lemma integral_complex_real_partial_eq_zero {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ∫ z, fderiv ℝ f z 1=0 := by
  let D (z : ℂ) := fderiv ℝ f z 1
  have hD : Continuous D := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDi : Integrable D := hD.integrable_of_hasCompactSupport (hs.fderiv_apply ℝ 1)
  have hline (y : ℝ) : ∫ x : ℝ, D ((x:ℂ)+(y:ℂ)*Complex.I)=0 := by
    let L (x : ℝ) := (x:ℂ)+(y:ℂ)*Complex.I
    have hLc : ContDiff ℝ 1 L := Complex.ofRealCLM.contDiff.add contDiff_const
    have hLi : Isometry L := by
      apply isometry_iff_dist_eq.mpr
      intro x x'
      simpa only [L,dist_add_right] using Complex.isometry_ofReal.dist_eq x x'
    have hcs : HasCompactSupport (f ∘ L) := hs.comp_isClosedEmbedding hLi.isClosedEmbedding
    have he (x : ℝ) : deriv (f ∘ L) x=D (L x) := by
      have hd := (hf.differentiable (by norm_num) (L x)).hasFDerivAt.comp_hasDerivAt x
        ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y:ℂ)*Complex.I))
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using hd.deriv
    simpa only [he] using integral_deriv_compact_eq_zero (hf.comp hLc) hcs
  let e := Complex.measurableEquivRealProd.symm
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hprod : Integrable (fun p : ℝ × ℝ => D (e p)) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mpr hDi
  rw [←hp.integral_comp e.measurableEmbedding]
  change (∫ p : ℝ × ℝ, D (e p))=0
  rw [Measure.volume_eq_prod] at hprod ⊢
  rw [integral_prod_symm _ hprod]
  have he (y : ℝ) : (∫ x : ℝ, D (e (x,y)))=0 := by
    have heq (x y : ℝ) : e (x,y)=(x:ℂ)+(y:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [e,Complex.measurableEquivRealProd_symm_apply]
    simpa only [heq] using hline y
  simp only [he,integral_zero]

end SLEExactGauge

end

end OAI
