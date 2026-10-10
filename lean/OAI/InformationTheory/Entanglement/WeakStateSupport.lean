import OAI.InformationTheory.Entanglement.WeakIntegralForm

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι X : Type*} [MeasurableSpace X]
def densityDiag (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) (i : ι) : ℝ :=
  (inner ℂ (b i) (ρ.val.val (b i))).re
omit [CompleteSpace H] in
lemma densityDiag_nonneg (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) (i : ι) :
    0≤densityDiag b ρ i := (nonneg_iff_isPositive.mp ρ.property.1).re_inner_nonneg_right _
omit [CompleteSpace H] in
lemma densityDiag_summable (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) :
    Summable (densityDiag b ρ) := ((traceClass_positive_iff b _).mp ⟨ρ.val.property,ρ.property.1⟩).2
omit [CompleteSpace H] in
lemma densityDiag_sum (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) : ∑' i, densityDiag b ρ i=1 := by
  change hilbertTrace b ρ.val.val=1
  rw [← traceClassTrace_re,ρ.property.2]
  rfl
lemma positive_re_inner_zero {A : H→L[ℂ]H} (hA : 0≤A) {x : H}
    (hx : (inner ℂ x (A x)).re=0) : A x=0 := by
  have hs : ‖CFC.sqrt A x‖^2=0 := by rwa [← positive_diagonal_sqrt hA]
  have hz : CFC.sqrt A x=0 := norm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp hs)
  rw [← CFC.sqrt_mul_sqrt_self A hA]
  change CFC.sqrt A (CFC.sqrt A x)=0
  rw [hz,map_zero]
omit [CompleteSpace H] in
lemma density_subtype_diag_le (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) (s : Set ι) :
    (∑' i : s, densityDiag b ρ i)≤1 := by
  rw [← densityDiag_sum b ρ]
  exact Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
    (fun i _ => densityDiag_nonneg b ρ i) (fun i => le_rfl)
    ((densityDiag_summable b ρ).subtype s) (densityDiag_summable b ρ)
lemma density_kills_outside (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) (s : Set ι)
    (hs : (∑' i : s, densityDiag b ρ i)=1) : ∀ i∉s, ρ.val.val (b i)=0 := by
  have he := (densityDiag_summable b ρ).tsum_subtype_add_tsum_subtype_compl s
  rw [hs,densityDiag_sum b ρ] at he
  have hh : (∑' i : ↥(sᶜ), densityDiag b ρ i)=0 := by linarith
  intro i hi
  apply positive_re_inner_zero ρ.property.1
  have hl := ((densityDiag_summable b ρ).subtype sᶜ).le_tsum (⟨i,hi⟩ : ↥(sᶜ))
    (fun j hj => densityDiag_nonneg b ρ j)
  change densityDiag b ρ i ≤ ∑' j : ↥(sᶜ), densityDiag b ρ j at hl
  rw [hh] at hl
  exact le_antisymm hl (densityDiag_nonneg b ρ i)

theorem weak_density_countable_support (b : HilbertBasis ι ℂ H)
    (μ : Measure X) [IsProbabilityMeasure μ] (ρ : X→DensityOperator b) (T : DensityOperator b)
    (hρ : ∀ x y : H, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hmean : ∀ x y : H, inner ℂ x (T.val.val y)=∫ z, inner ℂ x ((ρ z).val.val y) ∂μ) :
    (Function.support (densityDiag b T)).Countable ∧
      ∀ᵐ z ∂μ, ∀ i∉Function.support (densityDiag b T), (ρ z).val.val (b i)=0 := by
  let s := Function.support (densityDiag b T)
  have hcount : s.Countable := (densityDiag_summable b T).countable_support
  let : Countable s := hcount.to_subtype
  have hdiag (i : ι) : Integrable (fun z => densityDiag b (ρ z) i) μ :=
    (density_coefficient_integrable b μ ρ hρ (b i) (b i)).re
  have hmean' (i : ι) : ∫ z, densityDiag b (ρ z) i ∂μ=densityDiag b T i := by
    change (∫ z, (inner ℂ (b i) ((ρ z).val.val (b i))).re ∂μ)=_
    erw [integral_re (density_coefficient_integrable b μ ρ hρ (b i) (b i))]
    exact congrArg Complex.re (hmean (b i) (b i)).symm
  have hnorm (i : s) : ∫ z, ‖densityDiag b (ρ z) i‖ ∂μ=densityDiag b T i := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (densityDiag_nonneg b (ρ _) _)] using hmean' i
  have hsum : Summable (fun i : s => ∫ z, ‖densityDiag b (ρ z) i‖ ∂μ) := by
    simp_rw [hnorm]
    exact (densityDiag_summable b T).subtype s
  let g := fun z => ∑' i : s, densityDiag b (ρ z) i
  have hgmean : ∫ z, g z ∂μ=1 := by
    have hh := (hasSum_integral_of_summable_integral_norm (fun i : s => hdiag i) hsum).tsum_eq
    rw [← hh]
    simp only [hmean']
    rw [tsum_subtype_eq_of_support_subset (show Function.support (densityDiag b T)⊆s from Set.Subset.rfl)]
    exact densityDiag_sum b T
  have hgm : Measurable g := by
    exact Measurable.tsum (fun i : s => (hρ (b i) (b i)).re)
  have hgn (z : X) : 0≤g z := tsum_nonneg (fun i => densityDiag_nonneg b (ρ z) i)
  have hgle (z : X) : g z≤1 := density_subtype_diag_le b (ρ z) s
  have hgi : Integrable g μ := by
    apply (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hgn z)] using hgle z)
  have hzero : ∀ᵐ z ∂μ, 1-g z=0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun z => sub_nonneg.mpr (hgle z))) ((integrable_const (1 : ℝ)).sub hgi)).mp
    rw [integral_sub (integrable_const (1 : ℝ)) hgi,hgmean]
    simp
  refine ⟨hcount,?_⟩
  filter_upwards [hzero] with z hz
  exact density_kills_outside b (ρ z) s (by linarith)

end SecretKey

end

end OAI
