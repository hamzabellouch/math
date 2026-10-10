import OAI.Probability.SLE.Multipoint.MultipointAbsorption

namespace OAI

/-! Relative derivatives of the finite product used in the multipoint
supermartingale. The off-diagonal sum is ordered, so its generator carries
the factor one half. -/

noncomputable section
open scoped BigOperators

namespace SLEExactGauge.Multipoint

lemma finite_product_hasDerivAt_relative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x)
    (hne : ∀ i ∈ s, f i x ≠ 0) :
    HasDerivAt (fun y => ∏ i ∈ s, f i y)
      ((∏ i ∈ s, f i x)*(∑ i ∈ s, df i/f i x)) x := by
  apply (HasDerivAt.fun_finsetProd hf).congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_eq_mul]
  rw [← Finset.mul_prod_erase s (fun i => f i x) hi]
  field_simp [hne i hi]

lemma sum_offDiag_mul {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b : ι → ℝ) :
    (∑ ij ∈ s.offDiag, b ij.1*b ij.2) =
      (∑ i ∈ s, b i)^2 - ∑ i ∈ s, (b i)^2 := by
  have he := Finset.sum_union (f := fun ij : ι × ι => b ij.1*b ij.2)
    (Finset.disjoint_diag_offDiag (s := s))
  rw [Finset.diag_union_offDiag, Finset.sum_product, ← Finset.sum_mul_sum, ← pow_two] at he
  have hdiag : (∑ ij ∈ s.diag, b ij.1*b ij.2) = ∑ i ∈ s, (b i)^2 := by
    simp only [Finset.diag, Finset.sum_map, Function.Embedding.coeFn_mk, Function.diag_apply,
      pow_two]
  rw [hdiag] at he
  linarith

lemma finite_product_second_relative {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i))
    (hdf : ∀ i ∈ s, Differentiable ℝ (deriv (f i)))
    (hne : ∀ y i, i ∈ s → f i y ≠ 0) (x : ℝ) :
    iteratedDeriv 2 (fun y => ∏ i ∈ s, f i y) x =
      (∏ i ∈ s, f i x)*((∑ i ∈ s, iteratedDeriv 2 (f i) x/f i x) +
        ∑ ij ∈ s.offDiag, (deriv (f ij.1) x/f ij.1 x)*(deriv (f ij.2) x/f ij.2 x)) := by
  let P := fun y => ∏ i ∈ s, f i y
  let b := fun i y => deriv (f i) y/f i y
  have hP (y : ℝ) : HasDerivAt P (P y*∑ i ∈ s, b i y) y :=
    finite_product_hasDerivAt_relative s f (fun i => deriv (f i) y) y
      (fun i hi => (hf i hi y).hasDerivAt) (hne y)
  have hPeq : deriv P = fun y => P y*∑ i ∈ s, b i y :=
    funext (fun y => (hP y).deriv)
  have hb (i : ι) (hi : i ∈ s) : HasDerivAt (b i)
      (iteratedDeriv 2 (f i) x/f i x-(b i x)^2) x := by
    apply (((hdf i hi x).hasDerivAt).div (hf i hi x).hasDerivAt (hne x i hi)).congr_deriv
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, b]
    field_simp [hne x i hi]
  have hsum := HasDerivAt.fun_sum (fun i hi => hb i hi)
  have hsecond := ((hP x).mul hsum).deriv
  change deriv (fun y => P y * ∑ i ∈ s, b i y) x = _ at hsecond
  change iteratedDeriv (1+1) P x = _
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hPeq, hsecond]
  rw [sum_offDiag_mul s (fun i => deriv (f i) x / f i x), Finset.sum_sub_distrib]
  dsimp only [P, b]
  ring

lemma finite_product_directional_relative {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E → ℝ) (z v : E)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z)
    (hne : ∀ i ∈ s, f i z ≠ 0) :
    (fderiv ℝ (fun z => ∏ i ∈ s, f i z) z) v =
      (∏ i ∈ s, f i z)*(∑ i ∈ s, (fderiv ℝ (f i) z) v/f i z) := by
  rw [fderiv_finsetProd hf, sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase s (fun i => f i z) hi]
  field_simp [hne i hi]

/-- Generator identity before estimating the individual and cross terms. -/
theorem finite_product_generator {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (F : ι → E → ℝ → ℝ)
    (hF : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => F i p.1 p.2))
    (hne : ∀ i ∈ s, ∀ z x, F i z x ≠ 0) (z v : E) (x : ℝ) :
    (fderiv ℝ (fun z => ∏ i ∈ s, F i z x) z) v +
        (1/2 : ℝ)*iteratedDeriv 2 (fun y => ∏ i ∈ s, F i z y) x =
      (∏ i ∈ s, F i z x)*
        ((∑ i ∈ s, ((fderiv ℝ (fun z => F i z x) z) v +
          (1/2 : ℝ)*iteratedDeriv 2 (F i z) x)/F i z x) +
        (1/2 : ℝ)*∑ ij ∈ s.offDiag,
          (deriv (F ij.1 z) x/F ij.1 z x)*(deriv (F ij.2 z) x/F ij.2 z x)) := by
  have hs (i : ι) (hi : i ∈ s) : ContDiff ℝ (⊤ : ℕ∞) (fun z => F i z x) :=
    (hF i hi).comp (contDiff_id.prodMk contDiff_const)
  have hx (i : ι) (hi : i ∈ s) : ContDiff ℝ (⊤ : ℕ∞) (F i z) :=
    (hF i hi).comp (contDiff_const.prodMk contDiff_id)
  rw [finite_product_directional_relative s (fun i z => F i z x) z v
    (fun i hi => ((hs i hi).differentiable (by simp)) z) (fun i hi => hne i hi z x)]
  rw [finite_product_second_relative s (fun i => F i z)
    (fun i hi => (hx i hi).differentiable (by simp))
    (fun i hi => ((hx i hi).of_le (by simp)).differentiable_deriv_two)
    (fun y i hi => hne i hi z y) x]
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end SLEExactGauge.Multipoint

end

end OAI
