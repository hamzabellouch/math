import Mathlib
import OAI.Probability.LogConcave.Analysis.CompactGibbsIbp

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma compact_slice_left {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {φ : E × F → ℝ} (hφ : HasCompactSupport φ) (z : F) :
    HasCompactSupport (fun y => φ (y,z)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft z,?_⟩
  convert isClosed_univ.prod (isClosed_singleton (x:=z)) using 1
  ext ⟨a,b⟩
  simp only [mem_range,Prod.mk.injEq,mem_prod,mem_univ,mem_singleton_iff,true_and]
  aesop

lemma compact_slice_right {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space E] {φ : E × F → ℝ} (hφ : HasCompactSupport φ) (y : E) :
    HasCompactSupport (fun z => φ (y,z)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight y,?_⟩
  convert (isClosed_singleton (x:=y)).prod isClosed_univ using 1
  ext ⟨a,b⟩
  simp only [mem_range,Prod.mk.injEq,mem_prod,mem_univ,mem_singleton_iff,and_true]
  aesop

lemma compact_derivative_field {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : HasCompactSupport φ) (W : E → E) :
    HasCompactSupport (fun p => fderiv ℝ φ p (W p)) := by
  apply HasCompactSupport.intro hφ.isCompact
  intro p hp
  rw [(HasFDerivAt.of_notMem_tsupport ℝ hp).fderiv]
  rfl

def skewCenteringField {d : ℕ} (K : Point d → Point d →L[ℝ] Point d)
    (m : Point d → Point d) (s : ℝ) (p : Point d × Point d) : Point d × Point d :=
  (-s⁻¹ • (K p.1).adjoint p.2,s⁻¹ • m p.1)

theorem product_stein_flux {d : ℕ} {μ : Measure (Point d)} [IsFiniteMeasure μ]
    {K : Point d → Point d →L[ℝ] Point d} {m : Point d → Point d}
    (hK : Continuous K) (hm : Continuous m)
    (hstein : ∀u : Point d,∀φ : Point d → ℝ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂μ)=∫y,fderiv ℝ φ y ((K y).adjoint u) ∂μ)
    (s : ℝ) {φ : Point d × Point d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) :
    (∫p,fderiv ℝ φ p (skewCenteringField K m s p) ∂μ.prod (stdGaussian (Point d)))=0 := by
  let ν := stdGaussian (Point d)
  let A := fun p : Point d × Point d => fderiv ℝ φ p ((K p.1).adjoint p.2,0)
  let B := fun p : Point d × Point d => fderiv ℝ φ p (0,m p.1)
  let C := fun p : Point d × Point d => inner ℝ p.2 (m p.1)*φ p
  have hD := hφ.continuous_fderiv (by norm_num)
  have hKA : Continuous (fun p : Point d × Point d => ((K p.1).adjoint p.2,(0:Point d))) :=
    (((ContinuousLinearMap.adjoint.continuous.comp hK).comp continuous_fst).clm_apply continuous_snd).prodMk continuous_const
  have hMB : Continuous (fun p : Point d × Point d => ((0:Point d),m p.1)) :=
    continuous_const.prodMk (hm.comp continuous_fst)
  have hAi : Integrable A (μ.prod ν) :=
    (hD.clm_apply hKA).integrable_of_hasCompactSupport (compact_derivative_field hφc _)
  have hBi : Integrable B (μ.prod ν) :=
    (hD.clm_apply hMB).integrable_of_hasCompactSupport (compact_derivative_field hφc _)
  have hCi : Integrable C (μ.prod ν) :=
    ((continuous_snd.inner (hm.comp continuous_fst)).mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hA (g : Point d) : (∫y,A (y,g) ∂μ)=∫y,C (y,g) ∂μ := by
    have hh := hstein g (fun y => φ (y,g)) (hφ.comp (contDiff_id.prodMk contDiff_const)) (compact_slice_left hφc g)
    have hd (y : Point d) : fderiv ℝ (fun y => φ (y,g)) y=
        (fderiv ℝ φ (y,g)).comp (ContinuousLinearMap.inl ℝ (Point d) (Point d)) := by
      exact ((hφ.differentiable (by norm_num) (y,g)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).prodMk (hasFDerivAt_const g y))).fderiv
    simpa only [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,A,C] using hh.symm
  have hB (y : Point d) : (∫g,B (y,g) ∂ν)=∫g,C (y,g) ∂ν := by
    have hh := compact_gaussian_ibp (g:=fun g => φ (y,g)) (hφ.comp (contDiff_const.prodMk contDiff_id)) (compact_slice_right hφc y) (m y)
    have hd (g : Point d) : fderiv ℝ (fun g => φ (y,g)) g=
        (fderiv ℝ φ (y,g)).comp (ContinuousLinearMap.inr ℝ (Point d) (Point d)) := by
      exact ((hφ.differentiable (by norm_num) (y,g)).hasFDerivAt.comp g
        ((hasFDerivAt_const y g).prodMk (hasFDerivAt_id g))).fderiv
    simpa only [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,B,C,ν] using hh
  have he (p : Point d × Point d) : fderiv ℝ φ p (skewCenteringField K m s p)=
      -s⁻¹*A p+s⁻¹*B p := by
    have he : skewCenteringField K m s p=
        (-s⁻¹) • ((K p.1).adjoint p.2,0)+s⁻¹ • (0,m p.1) := by
      ext <;> simp [skewCenteringField]
    rw [he,map_add,map_smul,map_smul]
    rfl
  simp_rw [he]
  rw [integral_add (hAi.const_mul _) (hBi.const_mul _),integral_const_mul,integral_const_mul]
  have hAC : (∫p,A p ∂μ.prod ν)=∫p,C p ∂μ.prod ν := by
    rw [integral_prod_symm _ hAi,integral_prod_symm _ hCi]
    exact integral_congr_ae (Filter.Eventually.of_forall hA)
  have hBC : (∫p,B p ∂μ.prod ν)=∫p,C p ∂μ.prod ν := by
    rw [integral_prod _ hBi,integral_prod _ hCi]
    exact integral_congr_ae (Filter.Eventually.of_forall hB)
  change -s⁻¹*(∫p,A p ∂μ.prod ν)+s⁻¹*(∫p,B p ∂μ.prod ν)=0
  rw [hAC,hBC]
  ring
end LogConcaveSampling

end

end

end

end OAI
