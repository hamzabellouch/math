import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli
import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerInput
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError

namespace OAI

/-! # The actual Laplacian after localizing a Poisson solution -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- A compact Lipschitz cutoff converts the local constant-source equation
into a global L² Laplacian. The gradient cross term is retained explicitly. -/
theorem IsConstantLaplacianOn.cutoff_weakLaplacian
    {Ω : Set X} (f η : SobolevSpace μ hQ) (c : ℝ)
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ η d)
    {χ : X → ℝ} {L B A : ℝ≥0} (hχ : LipschitzWith L χ)
    (hs : HasCompactSupport χ) (hb : ∀ x, |χ x| ≤ B) (hn : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ A) :
    ∃ q : Lp ℝ 2 μ,
      IsWeakLaplacian μ hQ (SobolevSpace.cutoffCLM μ hQ hχ hs hb hn f) q ∧
      q =ᵐ[μ] fun x => c*χ x+SobolevSpace.toLp μ hQ f x*d x+
        2*localGamma μ hQ f η x := by
  let F := SobolevSpace.toLp μ hQ f
  let M := SobolevSpace.cutoffCLM μ hQ hχ hs hb hn
  have hηB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ B := hη.mono fun x hx => hx ▸ hb x
  have hηG : ∀ᵐ x ∂μ, localGamma μ hQ η η x ≤ (L:ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ η,SobolevSpace.minimalSlope_le_lipschitz μ hQ η hχ hη,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ η)] with x he hg h0
    rw [he]
    exact pow_le_pow_left₀ h0 hg 2
  have hγ : MemLp (localGamma μ hQ f η) 2 μ := by
    simpa only [Measure.restrict_univ] using
      localGamma_memLp_two_of_bound μ hQ univ f η
        (by simpa only [Measure.restrict_univ] using hηG)
  have hFm : MemLp F ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable F) A
    (by simpa only [Real.norm_eq_abs] using hA)
  have hχm : MemLp χ 2 μ := (memLp_congr_ae hη).mp (Lp.memLp _)
  have hmQ : MemLp (fun x => c*χ x+F x*d x+2*localGamma μ hQ f η x) 2 μ := by
    simpa only [Pi.add_apply,Pi.mul_apply,mul_comm] using!
      ((hχm.const_mul c).add ((Lp.memLp d).mul hFm)).add (hγ.const_mul 2)
  let q := hmQ.toLp _
  have hq : q =ᵐ[μ] fun x => c*χ x+F x*d x+2*localGamma μ hQ f η x := hmQ.coeFn_toLp
  refine ⟨q,?_,hq⟩
  apply weakLaplacian_of_bounded_tests μ hQ
  intro g D hg
  let G := SobolevSpace.toLp μ hQ g
  have hi : Integrable (fun x => χ x*localGamma μ hQ f g x) μ :=
    (localGamma_memL1 μ hQ f g).bdd_mul hχ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hj : Integrable (fun x => F x*localGamma μ hQ η g x) μ :=
    (localGamma_memL1 μ hQ η g).bdd_mul (Lp.aestronglyMeasurable F)
      (by simpa only [Real.norm_eq_abs] using hA)
  have hk : Integrable (fun x => G x*localGamma μ hQ f η x) μ :=
    (localGamma_memL1 μ hQ f η).bdd_mul (Lp.aestronglyMeasurable G)
      (by simpa only [Real.norm_eq_abs] using hg)
  have hχG : Integrable (fun x => χ x*G x) μ := (hχm.integrable_mul (Lp.memLp G))
  have hdFG : Integrable (fun x => F x*d x*G x) μ := by
    convert ((Lp.memLp d).integrable_mul (Lp.memLp G)).bdd_mul (Lp.aestronglyMeasurable F)
      (by simpa only [Real.norm_eq_abs] using hA) using 1
    funext x
    change F x*d x*G x = F x*(d x*G x)
    ring
  have hform : energyForm μ hQ (M f) g =
      (∫ x, χ x*localGamma μ hQ f g x ∂μ)+(∫ x, F x*localGamma μ hQ η g x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hi hj]
    exact integral_congr_ae (localGamma_cutoffCLM μ hQ f η g hχ hs hb hn hη)
  have htest : energyForm μ hQ f (M g) =
      (∫ x, χ x*localGamma μ hQ f g x ∂μ)+(∫ x, G x*localGamma μ hQ f η x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hi hk]
    exact integral_congr_ae (localGamma_cutoffCLM_right μ hQ g η f hχ hs hb hn hη)
  have hconst : energyForm μ hQ f (M g) = -c*(∫ x, χ x*G x ∂μ) := by
    rw [hf (M g) (SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hχ hs hb hn hsupp g)]
    congr 1
    rw [integral_congr_ae (ae_restrict_of_ae (SobolevSpace.cutoffCLM_coe μ hQ hχ hs hb hn g))]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact Eventually.of_forall fun x hx => by
      have hz : χ x = 0 := by
        by_contra hne
        exact hx (hsupp (subset_tsupport χ hne))
      rw [hz,zero_mul]
  have heta : energyForm μ hQ η (SobolevSpace.product μ hQ f g A D) =
      (∫ x, F x*localGamma μ hQ η g x ∂μ)+(∫ x, G x*localGamma μ hQ f η x ∂μ) := by
    rw [← integral_localGamma_eq_energyForm,← integral_add hj hk]
    apply integral_congr_ae
    filter_upwards [localGamma_product_right μ hQ η f g A D hA hg,
      localGamma_comm μ hQ η f] with x hp hc
    rw [hp,hc]
  have hsource : energyForm μ hQ η (SobolevSpace.product μ hQ f g A D) =
      -(∫ x, F x*d x*G x ∂μ) := by
    rw [hd,L2.inner_def]
    simp only [Real.inner_apply]
    congr 1
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ f g A D hA hg] with x hx
    change d x*SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f g A D) x = _
    rw [hx]
    ring
  have hinner : inner ℝ q G = c*(∫ x, χ x*G x ∂μ)+
      (∫ x, F x*d x*G x ∂μ)+2*(∫ x, G x*localGamma μ hQ f η x ∂μ) := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    have heq : (fun x => q x*G x) =ᵐ[μ]
        fun x => c*(χ x*G x)+F x*d x*G x+2*(G x*localGamma μ hQ f η x) := by
      filter_upwards [hq] with x hx
      rw [hx]
      ring
    have hadd : Integrable (fun x => c*(χ x*G x)+F x*d x*G x) μ := by
      simpa only [Pi.add_apply] using! (hχG.const_mul c).add hdFG
    rw [integral_congr_ae heq,integral_add hadd (hk.const_mul 2),
      integral_add (hχG.const_mul c) hdFG,integral_const_mul,integral_const_mul]
  rw [hform]
  change _ = -inner ℝ q G
  rw [hinner]
  linarith only [htest,hconst,heta,hsource]

end RegularPointCoordinates

end

end OAI
