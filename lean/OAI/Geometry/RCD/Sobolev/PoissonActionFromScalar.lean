import OAI.Geometry.RCD.Sobolev.LocalPoissonMixedShifted
import OAI.Geometry.RCD.Sobolev.PoissonShiftedMeasure
import OAI.Geometry.RCD.Sobolev.HessianActionInput

namespace OAI

/-! # The exact mixed-action input from scalar dimensional Bochner

The same full measure appears in the local source identity, shifted
positivity and every mixed-action estimate. Separate direction caps are
retained, as required by the coordinate commutator.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_shifted_action_data_of_scalar {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (κ : ℝ) (hK : -κ≤K) (p : X) {r : ℝ} (hr : 0<r)
    (L : ℝ≥0) (U : Euclidean (n+2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n+2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) (U v) (ell v))
    (hL : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x≤(L:ℝ)^2*‖v‖^2)
    (M : PositiveBilinearMeasure X (Euclidean (n+2)))
    (hM : ∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v))
    (t : ℝ) (ht : t≤2*r) :
    ∃ G : ∀ v w, LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) (U v) (U w),
      ∀ v w z (b : ℝ),
        let H := localHessianAction (hausdorff n X) hX.quadratic (U v) (U w) (U z)
          (G v w).mixed (G v z).mixed (G w z).mixed
        MemLp (fun x => H x-b*localGamma (hausdorff n X) hX.quadratic (U w) (U z) x)
          2 ((hausdorff n X).restrict (ball p t)) ∧
        ∀ Cw Cz : ℝ, 0≤Cw → 0≤Cz →
          (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
            localGamma (hausdorff n X) hX.quadratic (U w) (U w) x≤Cw^2) →
          (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
            localGamma (hausdorff n X) hX.quadratic (U z) (U z) x≤Cz^2) →
          (∫ x in ball p t, (H x-b*localGamma (hausdorff n X) hX.quadratic (U w) (U z) x)^2
            ∂hausdorff n X)≤(Cw^2*Cz^2)*((M.measure v).real (ball p t)-
              (2*b*ell v-(n:ℝ)*b^2)*(hausdorff n X).real (ball p t)) := by
  classical
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let : IsFiniteMeasure (μ.restrict (ball p t)) := ⟨by
    simpa only [Measure.restrict_apply_univ,μ] using
      hX.finiteOnBounded (ball p t) isBounded_ball⟩
  have hgrad (v) : ∀ᵐ x ∂μ.restrict (ball p (8*r)),
      localGamma μ hQ (U v) (U v) x≤(L*‖v‖₊:ℝ≥0)^2 := by
    simpa only [NNReal.coe_mul,coe_nnnorm,mul_pow] using hL v
  have hpair (v w) := hX.local_poisson_hessian_pairing hn (U v) (U w)
    (ell v) (ell w) hr ht (hU v) (hU w) (L*‖v‖₊) (L*‖w‖₊) (hgrad v) (hgrad w)
  let G (v w) := Classical.choice (hpair v w)
  refine ⟨G,?_⟩
  intro v w z b
  let E := Classical.choice (hM v)
  have hσ : IsMeasureLaplacianOn μ hQ (ball p (2*r)) E.energy
      ((2:ℝ) • (M.measure v).toSignedMeasure-(2*κ) • μ.withDensityᵥ
        (localGamma μ hQ (U v) (U v))) := by
    rw [M.measure_toSignedMeasure]
    exact E.measure_laplacian
  obtain ⟨Fga,Fgz,Gaz,hga,hgz,haz,hbound⟩ := hX.local_poisson_mixed_shifted_bound
    hn hscalar (U v) (U w) (U z) (ell v) (ell w) (ell z) κ hK hr
    (hU v) (hU w) (hU z) (L*‖v‖₊) (L*‖w‖₊) (L*‖z‖₊)
    (hgrad v) (hgrad w) (hgrad z) E.energy (M.measure v) E.representative hσ
  have hs : ball p t ⊆ ball p (2*r) := ball_subset_ball ht
  have hga' : SobolevSpace.toLp μ hQ Fga =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ (G v w).mixed :=
    by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hga,(G v w).mixed_rep]
        with x hx hy
      exact hx.trans hy.symm
  have hgz' : SobolevSpace.toLp μ hQ Fgz =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ (G v z).mixed :=
    by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hs hgz,(G v z).mixed_rep]
        with x hx hy
      exact hx.trans hy.symm
  have haz' : SobolevSpace.toLp μ hQ Gaz =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ (G w z).mixed :=
    by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hs haz,(G w z).mixed_rep]
        with x hx hy
      exact hx.trans hy.symm
  let H := fun x => localHessianAction μ hQ (U v) (U w) (U z)
    (G v w).mixed (G v z).mixed (G w z).mixed x-b*localGamma μ hQ (U w) (U z) x
  have hb : ∀ᵐ x ∂μ.restrict (ball p t), (H x)^2≤
      (((M.measure v).rnDeriv μ x).toReal-(2*b*ell v-(n:ℝ)*b^2))*
        localGamma μ hQ (U w) (U w) x*localGamma μ hQ (U z) (U z) x := by
    have he := localHessianAction_congr μ hQ (f := U v) (f' := U v)
      (u := U w) (u' := U w) (v := U z) (v' := U z)
      EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl hga' hgz' haz'
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs (hbound b),he] with x hx he
    rwa [he] at hx
  have hd := ae_restrict_of_ae_restrict_of_subset hs
    (hX.poisson_measure_shifted_density hn hscalar κ hK p hr L U ell hU hL M hM v b)
  have hm : AEStronglyMeasurable H (μ.restrict (ball p t)) :=
    ((localHessianAction_integrable μ hQ (U v) (U w) (U z)
      (G v w).mixed (G v z).mixed (G w z).mixed).sub
        ((localGamma_memL1 μ hQ (U w) (U z)).const_mul b)).aestronglyMeasurable.restrict
  have hnonneg (a) : ∀ᵐ x ∂μ.restrict (ball p t), 0≤localGamma μ hQ (U a) (U a) x := by
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ (U a))] with x hx
    rw [hx]
    positivity
  have hcap (a) : ∀ᵐ x ∂μ.restrict (ball p t),
      localGamma μ hQ (U a) (U a) x≤(L:ℝ)^2*‖a‖^2 :=
    ae_restrict_of_ae_restrict_of_subset (hs.trans (ball_subset_ball (by linarith))) (hL a)
  have hh := memLp_two_of_shifted_radon_product μ (M.measure v) hm
    (2*b*ell v-(n:ℝ)*b^2) ((L:ℝ)^2*‖w‖^2) ((L:ℝ)^2*‖z‖^2)
    (by positivity) (by positivity) hd ((hnonneg w).and (hcap w)) ((hnonneg z).and (hcap z)) hb
  refine ⟨hh.1,?_⟩
  intro Cw Cz _ _ hw hz
  exact (memLp_two_of_shifted_radon_product μ (M.measure v) hm
    (2*b*ell v-(n:ℝ)*b^2) (Cw^2) (Cz^2) (sq_nonneg _) (sq_nonneg _) hd
    ((hnonneg w).and hw) ((hnonneg z).and hz) hb).2

/-- Scalar weak Bakry--Émery gives the local Hessian action bound. -/
theorem NoncollapsedRCD.poisson_hessian_action_input_of_scalar {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n) :
    LocalPoissonHessianActionInput hX := by
  intro κ _ hK p r hr L U ell hU hL
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : IsFiniteMeasure ((hausdorff n X).restrict (ball p (2*r))) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      hX.finiteOnBounded (ball p (2*r)) isBounded_ball⟩
  obtain ⟨M,hM,_⟩ := hX.poisson_second_order_data hn κ hK p hr L U ell hU hL
  refine ⟨M,hM,?_,?_⟩
  · exact shiftedBochnerLowerBound_of_density (hausdorff n X) M ell n
      (hX.poisson_measure_shifted_density hn hscalar κ hK p hr L U ell hU hL M hM)
  · intro t _ ht
    exact hX.poisson_shifted_action_data_of_scalar hn hscalar κ hK p hr L U ell hU hL M hM t ht

end RegularPointCoordinates

end

end OAI
