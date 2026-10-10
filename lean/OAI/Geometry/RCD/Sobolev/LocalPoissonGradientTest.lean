import OAI.Geometry.RCD.Coordinates.RegularCoreGradientProduct
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Coordinates.LocalConstantRepresentative
import OAI.Geometry.RCD.Metric.LocalDensitySource
import OAI.Geometry.RCD.Sobolev.LocalPoissonDimensionalDensity

namespace OAI

/-! # Gradient-product tests for actual local Poisson functions -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_gradient_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a : SobolevSpace (hausdorff n X) hX.quadratic) (c d κ : ℝ) (hK : -κ≤K)
    {p : X} {r t : ℝ} (hr : 0<r) (ht : t≤2*r)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) a d)
    (L M : ℝ≥0)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2)
    (hM : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic a a x≤(M:ℝ)^2)
    (F₀ A₀ G : SobolevSpace (hausdorff n X) hX.quadratic)
    (σ τ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f f)
    (hA₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic A₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic a a)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      ((2:ℝ) • σ.toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic f f)))
    (hτ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) A₀
      ((2:ℝ) • τ.toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic a a)))
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G
      =ᵐ[(hausdorff n X).restrict (ball p t)] localGamma (hausdorff n X) hX.quadratic f a)
    (b Cv Cw : ℝ)
    (hCv : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic f f x≤Cv^2)
    (hCw : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic a a x≤Cw^2)
    (g : compactLaplacianCore (hausdorff n X) hX.quadratic univ) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      (localGamma (hausdorff n X) hX.quadratic (G-b • a) g.val x)^2≤
        (2*Cw^2*((σ.rnDeriv (hausdorff n X) x).toReal-(2*b*c-(n:ℝ)*b^2))+
          2*Cv^2*(τ.rnDeriv (hausdorff n X) x).toReal)*
            localGamma (hausdorff n X) hX.quadratic g.val g.val x := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨F,qf,hqf,hFr,hqc⟩ := hX.local_poisson_regular_extension hn f c
    (R := 3*r) (by positivity) (by linarith) hf L hL
  obtain ⟨A,qa,hqa,hAr,hqd⟩ := hX.local_poisson_regular_extension hn a d
    (R := 3*r) (by positivity) (by linarith) ha M hM
  have h23 : ball p (2*r) ⊆ ball p (3*r) := ball_subset_ball (by linarith)
  have hF : SobolevSpace.toLp μ hQ F.val =ᵐ[μ.restrict (ball p (2*r))]
      SobolevSpace.toLp μ hQ f := ae_restrict_of_ae_restrict_of_subset h23 hFr
  have hA : SobolevSpace.toLp μ hQ A.val =ᵐ[μ.restrict (ball p (2*r))]
      SobolevSpace.toLp μ hQ a := ae_restrict_of_ae_restrict_of_subset h23 hAr
  obtain ⟨df,hdf,hdfc⟩ := hX.local_constant_representative hn p (2*r) c
  obtain ⟨da,hda,hdad⟩ := hX.local_constant_representative hn p (2*r) d
  have hsf : qf =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ hQ df := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h23 hqc,hdfc] with x hx hy
    exact hx.trans hy.symm
  have hsa : qa =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ hQ da := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h23 hqd,hdad] with x hx hy
    exact hx.trans hy.symm
  have hE : SobolevSpace.toLp μ hQ F₀ =ᵐ[μ.restrict (ball p (2*r))]
      localGamma μ hQ F.val F.val := hF₀.trans (localGamma_pair_congr_ae μ hQ hF hF).symm
  have hEa : SobolevSpace.toLp μ hQ A₀ =ᵐ[μ.restrict (ball p (2*r))]
      localGamma μ hQ A.val A.val := hA₀.trans (localGamma_pair_congr_ae μ hQ hA hA).symm
  have hsσ := hσ.bochner_constant_source_shifted μ hQ measurableSet_ball κ F₀ f F.val df c
    σ.toSignedMeasure hF hdfc
  have hsτ := hτ.bochner_constant_source_shifted μ hQ measurableSet_ball κ A₀ a A.val da d
    τ.toSignedMeasure hA hdad
  obtain ⟨FG,_,_,hFG,_,_,_,_⟩ := hX.regular_core_triple_hessian_on_measure hn hscalar F A 0
    p (by positivity : 0<2*r) df qf hqf ‖c‖₊ hdf hsf hK F₀ σ hE hsσ
  have hFGR : SobolevSpace.toLp μ hQ FG =ᵐ[μ.restrict (ball p (2*r))]
      localGamma μ hQ F.val A.val := ae_restrict_of_ae hFG
  have hb := hX.regular_core_gradient_product_test hn hscalar F A g p
    (by positivity : 0<2*r) df da qf qa hqf hqa ‖c‖₊ ‖d‖₊ hdf hda hsf hsa
    c hdfc hK F₀ A₀ FG σ τ hE hEa hFGR hsσ hsτ b
  have hs : ball p t ⊆ ball p (2*r) := ball_subset_ball ht
  have hrep : SobolevSpace.toLp μ hQ FG =ᵐ[μ.restrict (ball p t)] SobolevSpace.toLp μ hQ G := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hFGR,
      ae_restrict_of_ae_restrict_of_subset hs (localGamma_pair_congr_ae μ hQ hF hA),hG]
      with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  have hsub : SobolevSpace.toLp μ hQ (FG-b • A.val) =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ (G-b • a) := by
    simp only [map_sub,map_smul]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ FG)
        (b • SobolevSpace.toLp μ hQ A.val)),
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ G)
        (b • SobolevSpace.toLp μ hQ a)),
      ae_restrict_of_ae (Lp.coeFn_smul b (SobolevSpace.toLp μ hQ A.val)),
      ae_restrict_of_ae (Lp.coeFn_smul b (SobolevSpace.toLp μ hQ a)),
      hrep,ae_restrict_of_ae_restrict_of_subset hs hA] with x hs1 hs2 hm1 hm2 hfg ha
    simp only [hs1,hs2,hm1,hm2,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hfg,ha]
  have hγ := localGamma_pair_congr_ae μ hQ (g := g.val) (g' := g.val) hsub EventuallyEq.rfl
  have hden := hX.local_poisson_shifted_density hn hscalar f c κ hK hr hf L hL F₀ σ hF₀ hσ b
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hb,hγ,
    ae_restrict_of_ae_restrict_of_subset hs (localGamma_pair_congr_ae μ hQ hF hF),
    ae_restrict_of_ae_restrict_of_subset hs (localGamma_pair_congr_ae μ hQ hA hA),
    ae_restrict_of_ae_restrict_of_subset hs hden,hCv,hCw,
    ae_restrict_of_ae (localGamma_self μ hQ g.val)] with x hx he hff haa hd hcv hcw hgg
  rw [he,hff,haa] at hx
  apply hx.trans
  apply mul_le_mul_of_nonneg_right _ (by rw [hgg]; positivity)
  exact add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcw (by norm_num)) (sub_nonneg.mpr hd))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcv (by norm_num)) ENNReal.toReal_nonneg)

end RegularPointCoordinates

end

end OAI
