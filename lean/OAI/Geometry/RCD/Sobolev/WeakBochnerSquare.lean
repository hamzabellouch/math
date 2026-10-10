import OAI.Geometry.RCD.Sobolev.WeakLaplacianWeightedProduct
import OAI.Geometry.RCD.Coordinates.RegularBochnerForm
import OAI.Geometry.RCD.Sobolev.HessianActionIntegral

namespace OAI

/-! # The Bochner square identity without differentiating the L² sources

All derivatives of the two source functions cancel after the weak
Laplacians are tested against bounded Sobolev products.
-/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The scalar mixed Bochner test expression, before finite-span assembly. -/
def mixedBochnerTest (K : ℝ) (f g : SobolevSpace μ hQ) (d e : Lp ℝ 2 μ)
    (F : SobolevSpace μ hQ) (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) : ℝ :=
  bochnerTestForm μ hQ (-K) F ψ+weightedLaplacianPair μ q d e+
    (1/2:ℝ)*(weightedGamma μ hQ d g ψ+weightedGamma μ hQ e f ψ)

omit [ProperSpace X] in
/-- The three-term Hessian action under a bounded test. -/
theorem weighted_localHessianAction (q : X →ᵇ ℝ) (f v u fv fu vu : SobolevSpace μ hQ) :
    (∫ x, q x*localHessianAction μ hQ f v u fv fu vu x ∂μ) =
      (weightedGamma μ hQ q v fu+weightedGamma μ hQ q u fv-weightedGamma μ hQ q f vu)/2 := by
  have hi (a b : SobolevSpace μ hQ) : Integrable (fun x => q x*localGamma μ hQ a b x) μ :=
    (localGamma_memL1 μ hQ a b).bdd_mul q.continuous.aestronglyMeasurable
      (Eventually.of_forall q.norm_coe_le_norm)
  have he : (fun x => q x*localHessianAction μ hQ f v u fv fu vu x) =
      fun x => (q x*localGamma μ hQ v fu x+q x*localGamma μ hQ u fv x-
        q x*localGamma μ hQ f vu x)/2 := by
    funext x
    unfold localHessianAction
    ring
  have hs : Integrable (fun x => q x*localGamma μ hQ v fu x+q x*localGamma μ hQ u fv x) μ := by
    simpa only [Pi.add_apply] using! (hi v fu).add (hi u fv)
  rw [he,integral_div,integral_sub hs (hi f vu),integral_add (hi v fu) (hi u fv)]
  rfl

/-- The exact square-product identity for bounded regular functions with
merely L² weak Laplacians. No Sobolev representative of either source is
required. -/
theorem mixedBochnerTest_square
    (K : ℝ) (f g F G ψ : SobolevSpace μ hQ) (d e ez : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ f d) (he : IsWeakLaplacian μ hQ g e)
    (A B C L M : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤A)
    (hF : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ F x|≤B)
    (hG : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ G x|≤C)
    (hfL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x≤L)
    (hgM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x≤M)
    (hFr : SobolevSpace.toLp μ hQ F =ᵐ[μ] localGamma μ hQ f g)
    (hGr : SobolevSpace.toLp μ hQ G =ᵐ[μ] localGamma μ hQ g g)
    (gb q : X →ᵇ ℝ) (hgb : SobolevSpace.toLp μ hQ g =ᵐ[μ] gb)
    (hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] q)
    (hez : ez =ᵐ[μ] fun x => 2*SobolevSpace.toLp μ hQ g x*e x+
      2*SobolevSpace.toLp μ hQ G x) :
    let z := SobolevSpace.product μ hQ g g A A
    let Fz := (2:ℝ) • SobolevSpace.product μ hQ g F A B
    let ψg := SobolevSpace.product μ hQ ψ g ‖q‖₊ A
    mixedBochnerTest μ hQ K f z d ez Fz q ψ =
      2*mixedBochnerTest μ hQ K f g d e F (q*gb) ψg+
        2*(∫ x, q x*localHessianAction μ hQ f g g F F G x ∂μ) := by
  let z := SobolevSpace.product μ hQ g g A A
  let Fz := (2:ℝ) • SobolevSpace.product μ hQ g F A B
  let ψg := SobolevSpace.product μ hQ ψ g ‖q‖₊ A
  have hψb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ ψ x|≤‖q‖₊ := by
    filter_upwards [hψ] with x hx
    rw [hx]
    exact q.norm_coe_le_norm x
  have hqn : ∀ᵐ x ∂μ, ‖q x‖≤(‖q‖₊:ℝ) := Eventually.of_forall q.norm_coe_le_norm
  have hiD : Integrable (fun x => q x*d x*SobolevSpace.toLp μ hQ G x) μ := by
    simpa only [Pi.mul_apply,mul_assoc] using!
      ((Lp.memLp d).integrable_mul (Lp.memLp (SobolevSpace.toLp μ hQ G))).bdd_mul
        q.continuous.aestronglyMeasurable hqn
  have hiE : Integrable (fun x => q x*e x*SobolevSpace.toLp μ hQ F x) μ := by
    simpa only [Pi.mul_apply,mul_assoc] using!
      ((Lp.memLp e).integrable_mul (Lp.memLp (SobolevSpace.toLp μ hQ F))).bdd_mul
        q.continuous.aestronglyMeasurable hqn
  let I := ∫ x, q x*d x*SobolevSpace.toLp μ hQ G x ∂μ
  let J := ∫ x, q x*e x*SobolevSpace.toLp μ hQ F x ∂μ
  have hsrc : weightedLaplacianPair μ q d ez=
      2*weightedLaplacianPair μ (q*gb) d e+2*I := by
    rw [weightedLaplacianPair_apply,weightedLaplacianPair_apply]
    have hi : Integrable (fun x => (q*gb) x*d x*e x) μ := by
      simpa only [Pi.mul_apply,mul_assoc] using!
        ((Lp.memLp d).integrable_mul (Lp.memLp e)).bdd_mul
          (q*gb).continuous.aestronglyMeasurable (Eventually.of_forall (q*gb).norm_coe_le_norm)
    have heq : (fun x => q x*d x*ez x) =ᵐ[μ]
        fun x => 2*((q*gb) x*d x*e x)+2*(q x*d x*SobolevSpace.toLp μ hQ G x) := by
      filter_upwards [hez,hgb] with x hz hx
      simp only [hz,BoundedContinuousFunction.mul_apply,← hx]
      ring
    rw [integral_congr_ae heq,integral_add (hi.const_mul 2) (hiD.const_mul 2),
      integral_const_mul,integral_const_mul]
  have hψg := SobolevSpace.product_coe μ hQ ψ g ‖q‖₊ A hψb hg
  have hΓg := localGamma_product_right μ hQ g ψ g ‖q‖₊ A hψb hg
  have hΓf := localGamma_product_right μ hQ f ψ g ‖q‖₊ A hψb hg
  have hΓz := localGamma_product_left μ hQ g g ψ A A hg hg
  have hwg : weightedGamma μ hQ d z ψ=2*weightedGamma μ hQ d g ψg-2*I := by
    have hi : Integrable (fun x => d x*localGamma μ hQ g ψg x) μ := by
      simpa only [Pi.mul_apply] using!
        (Lp.memLp d).integrable_mul (localGamma_memLp_of_bounded_gradient μ hQ g ψg M hgM)
    have heq : (fun x => d x*localGamma μ hQ z ψ x) =ᵐ[μ]
        fun x => 2*(d x*localGamma μ hQ g ψg x)-2*(q x*d x*SobolevSpace.toLp μ hQ G x) := by
      filter_upwards [hΓz,hΓg,hGr,hψ] with x hz htest hgr hp
      change localGamma μ hQ g ψg x=_ at htest
      change localGamma μ hQ z ψ x=_ at hz
      rw [hz,htest,hp,← hgr]
      ring
    unfold weightedGamma
    rw [integral_congr_ae heq,integral_sub (hi.const_mul 2) (hiD.const_mul 2),
      integral_const_mul,integral_const_mul]
  have hwf : weightedGamma μ hQ ez f ψ=2*weightedGamma μ hQ e f ψg+
      2*weightedGamma μ hQ (SobolevSpace.toLp μ hQ G) f ψ-2*J := by
    have hi : Integrable (fun x => e x*localGamma μ hQ f ψg x) μ := by
      simpa only [Pi.mul_apply] using!
        (Lp.memLp e).integrable_mul (localGamma_memLp_of_bounded_gradient μ hQ f ψg L hfL)
    have hj := (localGamma_memL1 μ hQ f ψ).bdd_mul
      (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ G))
      (by simpa only [Real.norm_eq_abs] using hG)
    have heq : (fun x => ez x*localGamma μ hQ f ψ x) =ᵐ[μ]
        fun x => 2*(e x*localGamma μ hQ f ψg x)+
          2*(SobolevSpace.toLp μ hQ G x*localGamma μ hQ f ψ x)-
            2*(q x*e x*SobolevSpace.toLp μ hQ F x) := by
      filter_upwards [hez,hΓf,hFr,hψ] with x hz htest hfr hp
      change localGamma μ hQ f ψg x=_ at htest
      rw [hz,htest,hp,← hfr]
      ring
    have hsum : Integrable (fun x => 2*(e x*localGamma μ hQ f ψg x)+
        2*(SobolevSpace.toLp μ hQ G x*localGamma μ hQ f ψ x)) μ := by
      simpa only [Pi.add_apply] using! (hi.const_mul 2).add (hj.const_mul 2)
    unfold weightedGamma
    rw [integral_congr_ae heq,integral_sub hsum (hiE.const_mul 2),
      integral_add (hi.const_mul 2) (hj.const_mul 2),integral_const_mul,
      integral_const_mul,integral_const_mul]
  have henergy : energyForm μ hQ Fz ψ=
      2*(weightedGamma μ hQ (SobolevSpace.toLp μ hQ g) F ψ+
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ F) g ψ) := by
    rw [energyForm_smul_left,energyForm_product_test μ hQ g F ψ A B hg hF]
  have htestenergy : energyForm μ hQ F ψg=
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ ψ) F g+
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ g) F ψ := by
    rw [energyForm_comm μ hQ F ψg,energyForm_product_test μ hQ ψ g F ‖q‖₊ A hψb hg,
      weightedGamma_comm μ hQ (SobolevSpace.toLp μ hQ ψ) g F,
      weightedGamma_comm μ hQ (SobolevSpace.toLp μ hQ g) ψ F]
  have hFz : SobolevSpace.toLp μ hQ Fz =ᵐ[μ]
      fun x => 2*SobolevSpace.toLp μ hQ g x*SobolevSpace.toLp μ hQ F x := by
    filter_upwards [Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g F A B)),
      SobolevSpace.product_coe μ hQ g F A B hg hF] with x hs hp
    dsimp only [Fz]
    simp only [map_smul]
    rw [hs]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hp]
    ring
  have hinner : inner ℝ (SobolevSpace.toLp μ hQ ψ) (SobolevSpace.toLp μ hQ Fz)=
      2*inner ℝ (SobolevSpace.toLp μ hQ ψg) (SobolevSpace.toLp μ hQ F) := by
    rw [L2.inner_def,L2.inner_def,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hFz,hψg] with x hf hp
    change SobolevSpace.toLp μ hQ ψg x = _ at hp
    simp only [Real.inner_apply]
    rw [hf,hp]
    ring
  have hif := hd.weighted_product μ hQ f G ψ d C ‖q‖₊ hG hψb
  have hig := he.weighted_product μ hQ g F ψ e B ‖q‖₊ hF hψb
  have hId : (∫ x, SobolevSpace.toLp μ hQ ψ x*SobolevSpace.toLp μ hQ G x*d x ∂μ)=I := by
    apply integral_congr_ae
    filter_upwards [hψ] with x hp
    rw [hp]
    ring
  have hJe : (∫ x, SobolevSpace.toLp μ hQ ψ x*SobolevSpace.toLp μ hQ F x*e x ∂μ)=J := by
    apply integral_congr_ae
    filter_upwards [hψ] with x hp
    rw [hp]
    ring
  rw [hId] at hif
  rw [hJe] at hig
  have hweight (a b : SobolevSpace μ hQ) : weightedGamma μ hQ q a b=
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ ψ) a b :=
    integral_congr_ae (hψ.symm.mono fun x hx => congrArg (fun t : ℝ => t*localGamma μ hQ a b x) hx)
  rw [weighted_localHessianAction μ hQ, hweight g F,hweight f G]
  dsimp only [mixedBochnerTest]
  rw [bochnerTestForm_apply,bochnerTestForm_apply,henergy,htestenergy,hinner,hsrc,hwg,hwf]
  rw [weightedGamma_comm μ hQ (SobolevSpace.toLp μ hQ ψ) F g]
  linarith only [hif,hig]

end RegularPointCoordinates

end

end OAI
