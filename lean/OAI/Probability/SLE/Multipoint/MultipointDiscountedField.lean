import OAI.Probability.SLE.Multipoint.MultipointProductGenerator

namespace OAI

/-! The smooth discounted product used between consecutive switches. -/

noncomputable section

namespace SLEExactGauge.Multipoint

def discountedProduct {ι : Type*} (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ)
    (z : (ι → ℂ × ℝ) × ℝ) (x : ℝ) : ℝ :=
  Real.exp (-z.2)*regularizedProduct s κ D σ z.1 x

lemma discountedProduct_contDiff {ι : Type*} [Fintype ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ((ι → ℂ × ℝ) × ℝ) × ℝ => discountedProduct s κ D σ p.1 p.2) := by
  unfold discountedProduct
  exact (contDiff_fst.snd.neg.exp).mul ((regularizedProduct_contDiff s κ D σ).comp
    (contDiff_fst.fst.prodMk contDiff_snd))

lemma discountedProduct_directional {ι : Type*} [Fintype ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ)
    (z v : ι → ℂ × ℝ) (b c x : ℝ) :
    (fderiv ℝ (fun q => discountedProduct s κ D σ q x) (z,b)) (v,c) =
      Real.exp (-b)*((fderiv ℝ (fun q => regularizedProduct s κ D σ q x) z) v -
        c*regularizedProduct s κ D σ z x) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun z => regularizedProduct s κ D σ z x) :=
    (regularizedProduct_contDiff s κ D σ).comp (contDiff_id.prodMk contDiff_const)
  have hd := ((hasFDerivAt_snd (𝕜 := ℝ) (p := (z,b))).neg.exp).mul
    (((hp.differentiable (by simp)) z).hasFDerivAt.comp (z,b) (hasFDerivAt_fst (𝕜 := ℝ)))
  have he := congrArg (fun f : ((ι → ℂ × ℝ) × ℝ) →L[ℝ] ℝ => f (v,c)) hd.fderiv
  change (fderiv ℝ (fun q => discountedProduct s κ D σ q x) (z,b)) (v,c) = _ at he
  rw [he]
  simp only [smul_apply, smul_eq_mul, add_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Function.comp_def,
    Pi.neg_apply]
  ring

lemma discountedProduct_spatial_second {ι : Type*} [Fintype ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (z : ι → ℂ × ℝ) (b x : ℝ) :
    iteratedDeriv 2 (discountedProduct s κ D σ (z,b)) x =
      Real.exp (-b)*iteratedDeriv 2 (regularizedProduct s κ D σ z) x := by
  apply iteratedDeriv_const_mul
  exact (((regularizedProduct_contDiff s κ D σ).comp
    (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffAt

lemma discountedProduct_directional_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i)
    (z v w : ι → ℂ × ℝ) (b c x : ℝ) (hvw : ∀ i ∈ s, v i = w i) :
    (fderiv ℝ (fun q => discountedProduct s κ D σ q x) (z,b)) (v,c) =
      (fderiv ℝ (fun q => discountedProduct s κ D σ q x) (z,b)) (w,c) := by
  rw [discountedProduct_directional, discountedProduct_directional,
    regularizedProduct_directional_congr s κ D σ hD z v w x hvw]

theorem discountedProduct_generator_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (z : ι → ℂ × ℝ) (b x : ℝ)
    (hD : ∀ i ∈ s, 0 < D i) (hσ : ∀ i ∈ s, σ i ≤ 1)
    (hδ : ∀ i ∈ s, branchRegulator κ (D i) (σ i) (z i) ≤ 1) :
    (fderiv ℝ (fun q => discountedProduct s κ D σ q x) (z,b))
        ((fun i => physicalLogLoewnerField (Real.sqrt κ*x) (z i)), productDriftCost s κ D σ z x) +
      (1/2 : ℝ)*iteratedDeriv 2 (discountedProduct s κ D σ (z,b)) x ≤ 0 := by
  rw [discountedProduct_directional, discountedProduct_spatial_second]
  have h := mul_le_mul_of_nonneg_left
    (regularizedProduct_generator_le s κ hκ hκ8 D σ z x hD hσ hδ) (Real.exp_pos (-b)).le
  nlinarith only [h]

end SLEExactGauge.Multipoint

end

end OAI
