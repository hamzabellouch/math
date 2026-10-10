import OAI.InformationTheory.Entanglement.MatrixMeasure

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder ENNReal MeasureTheory Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter
namespace SecretKey
open ChannelCompletion
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {n : Type} [Fintype n]

def quadratic (M : Mat n) (z : n → ℂ) : ℂ := ∑ i, ∑ j, star (z i)*M i j*z j
lemma quadratic_eq (M : Mat n) (z : n → ℂ) : quadratic M z=star z ⬝ᵥ M *ᵥ z := by
  simp only [quadratic,dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,mul_assoc]
lemma continuous_quadratic (M : Mat n) : Continuous (quadratic M) := by
  unfold quadratic
  fun_prop
lemma quadratic_integrable {D : Ω → Mat n}
    (hi : ∀ i j, Integrable (fun x => D x i j) μ) (z : n → ℂ) :
    Integrable (fun x => quadratic (D x) z) μ := by
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hi i j).const_mul _).mul_const _
namespace PositiveMatrixMeasure
variable (W : PositiveMatrixMeasure Ω n) [SigmaFinite μ]
variable (hdom : ∀ s, MeasurableSet s → μ s=0 → (Matrix.trace (W.value s)).re=0)
include hdom
lemma quadratic_setIntegral {s : Set Ω} (hs : MeasurableSet s) (z : n → ℂ) :
    (∫ x in s, quadratic (W.density μ x) z ∂μ)=quadratic (W.value s) z := by
  unfold quadratic
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (((W.density_integrable i j).const_mul _).mul_const _).integrableOn)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ =>
    (((W.density_integrable i j).const_mul _).mul_const _).integrableOn)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_mul_const,integral_const_mul,W.density_setIntegral hdom hs]
lemma density_ae_hermitian : ∀ᵐ x ∂μ, (W.density μ x).IsHermitian := by
  have h (i j : n) : (fun x => star (W.density μ x j i)) =ᵐ[μ] (fun x => W.density μ x i j) := by
    refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (RCLike.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
        (W.density_integrable j i)) (W.density_integrable i j) ?_
    intro s hs _
    change (∫ x in s, (starRingEnd ℂ) (W.density μ x j i) ∂μ)=_
    rw [integral_conj,W.density_setIntegral hdom hs,W.density_setIntegral hdom hs]
    exact congrArg (fun M : Mat n => M i j) (W.positive s hs).isHermitian.eq
  have hall := ae_all_iff.mpr fun i => ae_all_iff.mpr (h i)
  filter_upwards [hall] with x hx
  ext i j
  exact hx i j
lemma quadratic_ae_nonneg (z : n → ℂ) : ∀ᵐ x ∂μ, 0≤quadratic (W.density μ x) z := by
  have hi := quadratic_integrable (W.density_integrable (μ := μ)) z
  have hre : ∀ᵐ x ∂μ, 0≤(quadratic (W.density μ x) z).re := by
    refine ae_nonneg_of_forall_setIntegral_nonneg hi.re ?_
    intro s hs _
    simp only [← RCLike.re_eq_complex_re]
    rw [integral_re hi.integrableOn,W.quadratic_setIntegral hdom hs,quadratic_eq]
    exact (W.positive s hs).re_dotProduct_nonneg z
  have him : (fun x => (quadratic (W.density μ x) z).im) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
    refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hi.im (integrable_zero _ _ _) ?_
    intro s hs _
    simp only [← RCLike.im_eq_complex_im]
    rw [integral_im hi.integrableOn,W.quadratic_setIntegral hdom hs,quadratic_eq,integral_zero]
    exact (Complex.nonneg_iff.mp ((W.positive s hs).dotProduct_mulVec_nonneg z)).2.symm
  filter_upwards [hre,him] with x hx hy
  exact Complex.nonneg_iff.mpr ⟨hx,hy.symm⟩

lemma density_ae_psd : ∀ᵐ x ∂μ, (W.density μ x).PosSemidef := by
  have hall := ae_all_iff.mpr (fun k : ℕ => W.quadratic_ae_nonneg hdom
    (TopologicalSpace.denseSeq (n → ℂ) k))
  filter_upwards [W.density_ae_hermitian hdom,hall] with x hherm hx
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun z => ?_
  rw [← quadratic_eq]
  exact (TopologicalSpace.denseRange_denseSeq (n → ℂ)).induction_on z
    (isClosed_le continuous_const (continuous_quadratic _)) hx
end PositiveMatrixMeasure

end SecretKey

end

end OAI
