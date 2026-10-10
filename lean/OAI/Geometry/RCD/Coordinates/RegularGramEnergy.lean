import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction
import OAI.Geometry.RCD.Coordinates.RegularCoreGradientProduct
import OAI.Geometry.RCD.Sobolev.DenseCoreGradientBound
import OAI.Geometry.RCD.Metric.ShiftedRadonSum

namespace OAI

/-! # Local energy of a harmonic/regular gradient pairing from full Bochner masses -/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_gram_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hK : K ≤ 0)
    (f a : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (p : X) {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (df da : SobolevSpace (hausdorff n X) hX.quadratic)
    (qf qa : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (hqa : IsWeakLaplacian (hausdorff n X) hX.quadratic a.val qa)
    (A B : ℝ≥0)
    (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hda : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic da x|≤B)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    (hsa : qa =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic da)
    (hc : SobolevSpace.toLp (hausdorff n X) hX.quadratic df
      =ᵐ[(hausdorff n X).restrict (ball p R)] fun _ => 0)
    {J : ℝ} (hJK : J ≤ K)
    (F₀ A₀ G : SobolevSpace (hausdorff n X) hX.quadratic)
    (σ τ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hA₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic A₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic a.val a.val)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val a.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J f.val f.val df df σ.toSignedMeasure))
    (hτ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) A₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J a.val a.val da da τ.toSignedMeasure))
    (Cf Ca : ℝ≥0)
    (hCf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic f.val f.val x ≤ (Cf:ℝ)^2)
    (hCa : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic a.val a.val x ≤ (Ca:ℝ)^2) :
    (∫ x in ball p t, localGamma (hausdorff n X) hX.quadratic G G x ∂hausdorff n X) ≤
      2*(Ca:ℝ)^2*σ.real (ball p t)+2*(Cf:ℝ)^2*τ.real (ball p t) := by
  have hscalar := hX.scalarBochner_nonpositive K n hn hK p
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsFiniteMeasure (μ.restrict (ball p t)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (ball p t) isBounded_ball⟩
  let D x := 2*(Ca:ℝ)^2*(σ.rnDeriv μ x).toReal+2*(Cf:ℝ)^2*(τ.rnDeriv μ x).toReal
  have hmass := integral_shifted_radon_sum_le μ σ τ (ball p t) 0 (2*(Ca:ℝ)^2) (2*(Cf:ℝ)^2)
    (by positivity) (by positivity)
  simp only [sub_zero,zero_mul] at hmass
  have hD : Integrable D (μ.restrict (ball p t)) := hmass.1
  have hD0 : ∀ᵐ x ∂μ.restrict (ball p t), 0 ≤ D x :=
    Eventually.of_forall fun x => add_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
  obtain ⟨χ,hχ,hχ1⟩ := hX.exists_open_regular_cutoff hn isOpen_ball
    (isCompact_closedBall p t) (closedBall_subset_ball htR)
  let V := SobolevSpace.cutoffCLM μ Q χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1) G
  have hVmem : V∈SobolevSpace.dirichlet μ Q (ball p R) :=
    SobolevSpace.cutoffCLM_mem_dirichlet μ Q χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) hχ G
  have hV : SobolevSpace.toLp μ Q V =ᵐ[μ.restrict (ball p t)] SobolevSpace.toLp μ Q G := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [SobolevSpace.cutoffCLM_coe μ Q χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) G] with x hx hxt
    change SobolevSpace.toLp μ Q (SobolevSpace.cutoffCLM μ Q χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) G) x = _
    rw [hx,hχ1 x (ball_subset_closedBall hxt),one_mul]
  have htest (g : compactLaplacianCore μ Q (ball p R)) :
      ∀ᵐ x ∂μ.restrict (ball p t), (localGamma μ Q G g.val x)^2≤D x*localGamma μ Q g.val g.val x := by
    have hgu : g.val∈compactLaplacianCore μ Q univ := by
      obtain ⟨⟨v,L,hv,hvc,_hvs,hvr⟩,hql⟩ := g.property
      exact ⟨⟨v,L,hv,hvc,subset_univ _,hvr⟩,hql⟩
    have hb := hX.regular_core_gradient_product_test hn hscalar f a ⟨g.val,hgu⟩ p
      (ht.trans htR) df da qf qa hqf hqa A B hdf hda hsf hsa 0 hc hJK F₀ A₀ G σ τ hF₀ hA₀ hG hσ hτ 0
    simp only [zero_smul,sub_zero,mul_zero,zero_pow (by decide : (2:ℕ)≠0)] at hb
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball htR.le) hb,hCf,hCa,
      ae_restrict_of_ae (localGamma_self μ Q g.val)] with x hb hf ha hg
    have hnn : 0 ≤ localGamma μ Q g.val g.val x := by rw [hg]; positivity
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hnn
    dsimp only [D]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ)≤2)) ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by norm_num : (0:ℝ)≤2)) ENNReal.toReal_nonneg)
  exact (hX.gradient_integral_le_of_core_tests hn isOpen_ball measurableSet_ball G D hD hD0 htest
    ⟨V,hVmem⟩ hV).trans hmass.2

end RegularPointCoordinates

end

end OAI
