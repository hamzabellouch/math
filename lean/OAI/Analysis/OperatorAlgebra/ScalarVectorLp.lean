import OAI.Analysis.ModularTheory.CoreSeparation

namespace OAI

/-! Elementary scalar/vector tensors in vector-valued L². These concrete
maps supply the finite scalar blocks for expectation amplification. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure ℝ)

def scalarVectorLp (f : Lp ℂ 2 μ) (x : H) : Lp H 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).compLpL 2 μ f

lemma scalarVectorLp_ae (f : Lp ℂ 2 μ) (x : H) :
    scalarVectorLp μ f x =ᵐ[μ] fun t => f t • x :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).coeFn_compLpL f

lemma scalarVectorLp_norm (f : Lp ℂ 2 μ) (x : H) :
    ‖scalarVectorLp μ f x‖ = ‖f‖ * ‖x‖ := by
  have hn : ‖scalarVectorLp μ f x‖ = ‖(‖x‖ : ℂ) • f‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [scalarVectorLp_ae μ f x, Lp.coeFn_smul (‖x‖ : ℂ) f] with t hv hs
    rw [hv, hs, Pi.smul_apply, norm_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_norm, mul_comm]
  rw [hn, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_comm]

lemma scalarVectorLp_add_right (f : Lp ℂ 2 μ) (x y : H) :
    scalarVectorLp μ f (x + y) = scalarVectorLp μ f x + scalarVectorLp μ f y := by
  apply Lp.ext
  filter_upwards [scalarVectorLp_ae μ f (x + y), scalarVectorLp_ae μ f x,
    scalarVectorLp_ae μ f y, Lp.coeFn_add (scalarVectorLp μ f x) (scalarVectorLp μ f y)]
    with t h h₁ h₂ hs
  rw [h, hs, Pi.add_apply, h₁, h₂, smul_add]

lemma scalarVectorLp_smul_right (f : Lp ℂ 2 μ) (x : H) (c : ℂ) :
    scalarVectorLp μ f (c • x) = c • scalarVectorLp μ f x := by
  apply Lp.ext
  filter_upwards [scalarVectorLp_ae μ f (c • x), scalarVectorLp_ae μ f x,
    Lp.coeFn_smul c (scalarVectorLp μ f x)] with t h h₁ hs
  rw [h, hs, Pi.smul_apply, h₁, smul_comm]

def scalarVectorLpCLM (f : Lp ℂ 2 μ) : H →L[ℂ] Lp H 2 μ :=
  ({ toFun := scalarVectorLp μ f
     map_add' := scalarVectorLp_add_right μ f
     map_smul' := fun c x => scalarVectorLp_smul_right μ f x c } : H →ₗ[ℂ] Lp H 2 μ).mkContinuous
    ‖f‖ (fun x => by
      change ‖scalarVectorLp μ f x‖ ≤ ‖f‖ * ‖x‖
      exact (scalarVectorLp_norm μ f x).le)

lemma scalarVectorLp_inner (f g : Lp ℂ 2 μ) (x y : H) :
    inner ℂ (scalarVectorLp μ f x) (scalarVectorLp μ g y) =
      inner ℂ f g * inner ℂ x y := by
  simp only [L2.inner_def]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [scalarVectorLp_ae μ f x, scalarVectorLp_ae μ g y] with t hf hg
  rw [hf, hg, inner_smul_left, inner_smul_right]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  ring

variable [CompleteSpace H]

lemma scalarVectorLp_pointwise (T : H →L[ℂ] H) (f : Lp ℂ 2 μ) (x : H) :
    pointwiseLpRepresentation μ T (scalarVectorLp μ f x) = scalarVectorLp μ f (T x) := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLpL (p := 2) (μ := μ) (scalarVectorLp μ f x),
    scalarVectorLp_ae μ f x, scalarVectorLp_ae μ f (T x)] with t hT hf hTx
  change (T.compLpL 2 μ (scalarVectorLp μ f x)) t = _
  rw [hT, hf, hTx, map_smul]

end WeakPureInfiniteness

end

end OAI
