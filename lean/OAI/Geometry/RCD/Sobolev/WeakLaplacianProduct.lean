import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # L² Laplacians of products of bounded Sobolev functions -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The product rule retains the mixed gradient term. A bounded gradient
of one factor suffices to make the resulting weak Laplacian belong to L². -/
theorem IsWeakLaplacian.product
    (f g : SobolevSpace μ hQ) (df dg : Lp ℝ 2 μ)
    (hdf : IsWeakLaplacian μ hQ f df) (hdg : IsWeakLaplacian μ hQ g dg)
    (A B L : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ B)
    (hL : ∀ᵐ x ∂μ, localGamma μ hQ g g x ≤ (L:ℝ)^2) :
    ∃ q : Lp ℝ 2 μ,
      IsWeakLaplacian μ hQ (SobolevSpace.product μ hQ f g A B) q ∧
      q =ᵐ[μ] fun x => SobolevSpace.toLp μ hQ g x*df x+
        SobolevSpace.toLp μ hQ f x*dg x+2*localGamma μ hQ f g x := by
  let F := SobolevSpace.toLp μ hQ f
  let G := SobolevSpace.toLp μ hQ g
  have hmF : MemLp F ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable F) A
    (by simpa only [Real.norm_eq_abs] using hA)
  have hmG : MemLp G ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable G) B
    (by simpa only [Real.norm_eq_abs] using hB)
  have hΓ : MemLp (localGamma μ hQ f g) 2 μ := by
    simpa only [Measure.restrict_univ] using localGamma_memLp_two_of_bound μ hQ univ f g
      (by simpa only [Measure.restrict_univ] using hL)
  have hGdf : MemLp (fun x => G x*df x) 2 μ := hmG.mul (Lp.memLp df)
  have hFdg : MemLp (fun x => F x*dg x) 2 μ := hmF.mul (Lp.memLp dg)
  have hm : MemLp (fun x => G x*df x+F x*dg x+2*localGamma μ hQ f g x) 2 μ := by
    simpa only [Pi.add_apply] using! (hGdf.add hFdg).add (hΓ.const_mul 2)
  let q := hm.toLp _
  have hq : q =ᵐ[μ] fun x => G x*df x+F x*dg x+2*localGamma μ hQ f g x := hm.coeFn_toLp
  refine ⟨q,?_,hq⟩
  apply weakLaplacian_of_bounded_tests μ hQ
  intro φ D hφ
  let P := SobolevSpace.toLp μ hQ φ
  have hi : Integrable (fun x => G x*localGamma μ hQ f φ x) μ :=
    (localGamma_memL1 μ hQ f φ).bdd_mul (Lp.aestronglyMeasurable G)
      (by simpa only [Real.norm_eq_abs] using hB)
  have hj : Integrable (fun x => F x*localGamma μ hQ g φ x) μ :=
    (localGamma_memL1 μ hQ g φ).bdd_mul (Lp.aestronglyMeasurable F)
      (by simpa only [Real.norm_eq_abs] using hA)
  have hk : Integrable (fun x => P x*localGamma μ hQ f g x) μ :=
    (localGamma_memL1 μ hQ f g).bdd_mul (Lp.aestronglyMeasurable P)
      (by simpa only [Real.norm_eq_abs] using hφ)
  have hi' : Integrable (fun x => G x*df x*P x) μ := hGdf.integrable_mul (Lp.memLp P)
  have hj' : Integrable (fun x => F x*dg x*P x) μ := hFdg.integrable_mul (Lp.memLp P)
  have hform : energyForm μ hQ (SobolevSpace.product μ hQ f g A B) φ =
      (∫ x, G x*localGamma μ hQ f φ x ∂μ)+(∫ x, F x*localGamma μ hQ g φ x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [localGamma_product_left μ hQ f g φ A B hA hB] with x hx
    rw [hx]
    ring
  have htestf : energyForm μ hQ f (SobolevSpace.product μ hQ g φ B D) =
      (∫ x, G x*localGamma μ hQ f φ x ∂μ)+(∫ x, P x*localGamma μ hQ f g x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hi hk]
    exact integral_congr_ae (localGamma_product_right μ hQ f g φ B D hB hφ)
  have htestg : energyForm μ hQ g (SobolevSpace.product μ hQ f φ A D) =
      (∫ x, F x*localGamma μ hQ g φ x ∂μ)+(∫ x, P x*localGamma μ hQ f g x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hj hk]
    apply integral_congr_ae
    filter_upwards [localGamma_product_right μ hQ g f φ A D hA hφ,
      localGamma_comm μ hQ g f] with x hx hc
    rw [hx,hc]
  have hsourcef : energyForm μ hQ f (SobolevSpace.product μ hQ g φ B D) =
      -(∫ x, G x*df x*P x ∂μ) := by
    rw [hdf,L2.inner_def]
    simp only [Real.inner_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ g φ B D hB hφ] with x hx
    change df x*SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g φ B D) x = _
    rw [hx]
    ring
  have hsourceg : energyForm μ hQ g (SobolevSpace.product μ hQ f φ A D) =
      -(∫ x, F x*dg x*P x ∂μ) := by
    rw [hdg,L2.inner_def]
    simp only [Real.inner_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ f φ A D hA hφ] with x hx
    change dg x*SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f φ A D) x = _
    rw [hx]
    ring
  have hinner : inner ℝ q P = (∫ x, G x*df x*P x ∂μ)+
      (∫ x, F x*dg x*P x ∂μ)+2*(∫ x, P x*localGamma μ hQ f g x ∂μ) := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    have heq : (fun x => q x*P x) =ᵐ[μ]
        fun x => G x*df x*P x+F x*dg x*P x+2*(P x*localGamma μ hQ f g x) := by
      filter_upwards [hq] with x hx
      rw [hx]
      ring
    have hsum : Integrable (fun x => G x*df x*P x+F x*dg x*P x) μ := by
      simpa only [Pi.add_apply] using! hi'.add hj'
    rw [integral_congr_ae heq,integral_add hsum (hk.const_mul 2),
      integral_add hi' hj',integral_const_mul]
  rw [hform]
  change _ = -inner ℝ q P
  rw [hinner]
  linarith only [htestf,htestg,hsourcef,hsourceg]

end RegularPointCoordinates

end

end OAI
