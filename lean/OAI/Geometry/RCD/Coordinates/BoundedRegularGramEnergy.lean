import OAI.Geometry.RCD.Coordinates.RegularGramEnergy
import OAI.Geometry.RCD.Coordinates.BoundedRegularLocalization
import OAI.Geometry.RCD.Sobolev.BochnerSourceLocality
import OAI.Geometry.RCD.Coordinates.RegularCoreRepresentative
import OAI.Geometry.RCD.Sobolev.CompactMixedEnergy

namespace OAI

/-! # A local mixed Gram for the actual bounded regular test

Only the test is cut off. The two prescribed full positive Bochner measures
are retained, so the estimate uses their original mass on the smaller ball.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_regular_gram_energy {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (f : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (a da : SobolevSpace (hausdorff n X) hX.quadratic)
    (hqa : IsWeakLaplacian (hausdorff n X) hX.quadratic a
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic da))
    (V : X → ℝ) {L A B : ℝ≥0} (hV : LipschitzWith L V)
    (hVa : SobolevSpace.toLp (hausdorff n X) hX.quadratic a =ᵐ[hausdorff n X] V)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic a x|≤A)
    (hB : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic da x|≤B)
    (p : X) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (htr : t < 2*r)
    (hq0 : qf =ᵐ[(hausdorff n X).restrict (ball p (2*r))] fun _ => 0)
    (F₀ A₀ : SobolevSpace (hausdorff n X) hX.quadratic)
    (σ τ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hA₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic A₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic a a)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic K f.val f.val 0 0 σ.toSignedMeasure))
    (hτ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) A₀
      (bochnerGramSource (hausdorff n X) hX.quadratic K a a da da τ.toSignedMeasure))
    (Cf Ca : ℝ≥0)
    (hCf : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic f.val f.val x ≤ (Cf:ℝ)^2)
    (hCa : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic a a x ≤ (Ca:ℝ)^2) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G
        =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f.val a) ∧
      (∫ x in ball p t, localGamma (hausdorff n X) hX.quadratic G G x ∂hausdorff n X) ≤
        2*(Ca:ℝ)^2*σ.real (ball p t)+2*(Cf:ℝ)^2*τ.real (ball p t) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨Cχ,_hCχ,⟨χ⟩⟩ := hX.goodCutoff_exists hn p (show 0 < 2*r by linarith)
  obtain ⟨a',qa',hqa',ha',hda'⟩ := bounded_regular_localization μ Q a
    (SobolevSpace.toLp μ Q da) hqa V hV hVa A hA χ
  obtain ⟨F,Lf,_Af,hF,hFc,hfr,_hAf⟩ := regular_core_representative μ Q f
  obtain ⟨W,La,_Aa,hW,hWc,hwr,_hAa⟩ := regular_core_representative μ Q a'
  obtain ⟨G,hG⟩ := hX.compact_mixed_energy hn p f.val a'.val hF hFc hfr hW hWc hwr qf qa' hqf hqa'
  have he := localGamma_pair_congr_ae μ Q (f := f.val) (f' := f.val) (g := a) (g' := a'.val)
    (EventuallyEq.refl _ _) ha'
  have hGr : SobolevSpace.toLp μ Q G =ᵐ[μ.restrict (ball p (2*r))] localGamma μ Q f.val a :=
    Filter.EventuallyEq.trans (ae_restrict_of_ae hG) he
  have hA' : SobolevSpace.toLp μ Q A₀ =ᵐ[μ.restrict (ball p (2*r))] localGamma μ Q a'.val a'.val :=
    hA₀.trans (Filter.EventuallyEq.symm (localGamma_pair_congr_ae μ Q ha' ha'))
  have hτ' := IsMeasureLaplacianOn.bochner_congr μ Q measurableSet_ball K τ.toSignedMeasure (Filter.EventuallyEq.symm ha') hτ
  have hCa' : ∀ᵐ x ∂μ.restrict (ball p t), localGamma μ Q a'.val a'.val x≤(Ca:ℝ)^2 := by
    filter_upwards [hCa,ae_restrict_of_ae_restrict_of_subset (ball_subset_ball htr.le)
      (localGamma_pair_congr_ae μ Q ha' ha')] with x hx he
    rw [he]
    exact hx
  have hz : SobolevSpace.toLp μ Q (0 : SobolevSpace μ Q) =ᵐ[μ] fun _ => (0:ℝ) := by
    simpa only [map_zero] using! (Lp.coeFn_zero ℝ 2 μ)
  have hzb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (0 : SobolevSpace μ Q) x|≤(0:ℝ≥0) := by
    filter_upwards [hz] with x hx
    simp only [hx,abs_zero,NNReal.coe_zero,le_refl]
  have hqzero : qf =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ Q (0 : SobolevSpace μ Q) :=
    hq0.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae hz))
  refine ⟨G,hGr,?_⟩
  exact hX.regular_gram_energy hn hK f a' p ht htr 0 da qf qa' hqf hqa'
    0 B hzb hB hqzero hda' (ae_restrict_of_ae hz) le_rfl F₀ A₀ G σ τ hF₀ hA'
    (ae_restrict_of_ae hG) hσ hτ' Cf Ca hCf hCa'

end RegularPointCoordinates

end

end OAI
