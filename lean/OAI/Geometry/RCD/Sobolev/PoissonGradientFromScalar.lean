import OAI.Geometry.RCD.Sobolev.LocalPoissonGradientTest
import OAI.Geometry.RCD.Sobolev.DenseCoreGradientBound
import OAI.Geometry.RCD.Metric.ShiftedRadonSum
import OAI.Geometry.RCD.Sobolev.PoissonShiftedMeasure
import OAI.Geometry.RCD.Sobolev.GradientProductInput

namespace OAI

/-! # The exact gradient-product input from scalar dimensional Bochner

The regular test algebra is dense. Testing against a compactly localized
copy of the actual mixed gradient proves the full Sobolev energy estimate.
No Laplacian or Lipschitz premise is imposed on that mixed representative.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_gradient_product_input_of_scalar {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n) :
    LocalPoissonGradientProductInput hX := by
  classical
  intro κ _ hK p r hr L U ell hU hL M hM t _ ht v w G hG b Cv Cw _ _ hCv hCw
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let : IsFiniteMeasure (μ.restrict (ball p t)) := ⟨by
    simpa only [Measure.restrict_apply_univ,μ] using
      hX.finiteOnBounded (ball p t) isBounded_ball⟩
  let E := Classical.choice (hM v)
  let F := Classical.choice (hM w)
  have hsource (a) : IsMeasureLaplacianOn μ hQ (ball p (2*r))
      (Classical.choice (hM a)).energy
      ((2:ℝ) • (M.measure a).toSignedMeasure-(2*κ) • μ.withDensityᵥ
        (localGamma μ hQ (U a) (U a))) := by
    rw [M.measure_toSignedMeasure]
    exact (Classical.choice (hM a)).measure_laplacian
  have hgrad (a) : ∀ᵐ x ∂μ.restrict (ball p (8*r)),
      localGamma μ hQ (U a) (U a) x≤(L*‖a‖₊:ℝ≥0)^2 := by
    simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hL a
  let D : X → ℝ := fun x =>
    2*Cw^2*(((M.measure v).rnDeriv μ x).toReal-(2*b*ell v-(n:ℝ)*b^2))+
      2*Cv^2*((M.measure w).rnDeriv μ x).toReal
  have hmass := integral_shifted_radon_sum_le μ (M.measure v) (M.measure w) (ball p t)
    (2*b*ell v-(n:ℝ)*b^2) (2*Cw^2) (2*Cv^2) (by positivity) (by positivity)
  have hD : Integrable D (μ.restrict (ball p t)) := hmass.1
  have hD0 : ∀ᵐ x ∂μ.restrict (ball p t), 0≤D x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball ht)
      (hX.poisson_measure_shifted_density hn hscalar κ hK p hr L U ell hU hL M hM v b)]
      with x hx
    exact add_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hx))
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
  obtain ⟨χ,hχ,hχ1⟩ := hX.exists_open_regular_cutoff hn isOpen_ball
    (isCompact_closedBall p (2*r)) (closedBall_subset_ball (by linarith : 2*r<3*r))
  let W := G-b • U w
  let V := SobolevSpace.cutoffCLM μ hQ χ.lipschitz χ.compact χ.abs_le
    (fun x => (χ.bounds x).1) W
  have hVmem : V∈SobolevSpace.dirichlet μ hQ (ball p (3*r)) :=
    SobolevSpace.cutoffCLM_mem_dirichlet μ hQ χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) hχ W
  have hV : SobolevSpace.toLp μ hQ V =ᵐ[μ.restrict (ball p t)] SobolevSpace.toLp μ hQ W := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) W] with x hx hxS
    change SobolevSpace.toLp μ hQ (SobolevSpace.cutoffCLM μ hQ χ.lipschitz χ.compact χ.abs_le
      (fun x => (χ.bounds x).1) W) x= _
    rw [hx,hχ1 x ((ball_subset_ball ht hxS |> ball_subset_closedBall)),one_mul]
  have htest (g : compactLaplacianCore μ hQ (ball p (3*r))) :
      ∀ᵐ x ∂μ.restrict (ball p t), (localGamma μ hQ W g.val x)^2≤D x*localGamma μ hQ g.val g.val x := by
    have hgu : g.val∈compactLaplacianCore μ hQ univ := by
      obtain ⟨⟨f,C,hf,hfc,_,hrep⟩,hlap⟩ := g.property
      exact ⟨⟨f,C,hf,hfc,subset_univ _,hrep⟩,hlap⟩
    exact hX.local_poisson_gradient_test hn hscalar (U v) (U w) (ell v) (ell w) κ hK hr ht
      (hU v) (hU w) (L*‖v‖₊) (L*‖w‖₊) (hgrad v) (hgrad w)
      E.energy F.energy G (M.measure v) (M.measure w) E.representative F.representative
      (hsource v) (hsource w) hG b Cv Cw hCv hCw ⟨g.val,hgu⟩
  have hi := hX.gradient_integral_le_of_core_tests hn isOpen_ball measurableSet_ball
    W D hD hD0 htest ⟨V,hVmem⟩ hV
  exact hi.trans hmass.2

end RegularPointCoordinates

end

end OAI
