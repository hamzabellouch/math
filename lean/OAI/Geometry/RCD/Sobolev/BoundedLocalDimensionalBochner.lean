import OAI.Geometry.RCD.Heat.BakryLedouxScalarBochner
import OAI.Geometry.RCD.Heat.NonpositiveBakryLedoux
import OAI.Geometry.RCD.Coordinates.BoundedRegularLocalization
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent
import OAI.Geometry.RCD.Sobolev.CompactEnergyDensity
import OAI.Geometry.RCD.Sobolev.CompactBochnerTest
import OAI.Geometry.RCD.Sobolev.WeakLaplacianMixedSourceL2
import OAI.Geometry.RCD.Sobolev.BochnerTestForm
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # Dimensional local Bochner inequality for bounded regular functions

Compact localization retains the original function and its L² source.
The source needs Sobolev regularity only for the displayed local mixed
pairing. The actual Bakry--Ledoux estimate retains the squared-source term;
no derivative of the cutoff source is used.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_local_dimensional_bochner {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (u d G w : SobolevSpace (hausdorff n X) hX.quadratic)
    (source : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u source)
    (v : X → ℝ) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] v)
    (A : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤A)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u)
    (p : X) {r : ℝ} (hr : 0<r)
    (hdlocal : source =ᵐ[(hausdorff n X).restrict (ball p r)]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic d)
    (q : X →ᵇ ℝ)
    (hq : tsupport q ⊆ ball p r) (hq0 : ∀ x, 0≤q x)
    (hw : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] q) :
    (1/(n:ℝ))*(∫ x, q x*(SobolevSpace.toLp (hausdorff n X) hX.quadratic d x)^2
      ∂hausdorff n X) ≤ bochnerTestForm (hausdorff n X) hX.quadratic (-K) G w -
      ∫ x, q x*localGamma (hausdorff n X) hX.quadratic u d x ∂hausdorff n X := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨C,-,⟨χ⟩⟩ := hX.goodCutoff_exists hn p hr
  obtain ⟨F,e,he,hFu,hed⟩ := bounded_regular_localization μ Q u source
    hd v hv hu A hA χ
  obtain ⟨z,M,hz,hzc,-,hFz⟩ := F.property.1
  obtain ⟨H,hH,-,-⟩ := hX.compact_energy_density hn hz hzc p F.val hFz e he
  have hBL := hX.bakryLedoux_nonpositive K n hn hK (le_refl (n:ℝ)) p
  have hboch := hBL.compact_bochner_sobolev_test hX hn hz hzc p F.val hFz e he H hH w
    q.continuous.measurable hw ‖q‖₊ (fun x => q.norm_coe_le_norm x) hq0
  have hwb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x|≤‖q‖₊ := by
    filter_upwards [hw] with x hx
    rw [hx]
    exact q.norm_coe_le_norm x
  have hed' : e =ᵐ[μ.restrict (ball p r)] SobolevSpace.toLp μ Q d := hed.trans hdlocal
  have hFgrad := SobolevSpace.minimalSlope_le_lipschitz μ Q F.val hz hFz
  have hmix := weakLaplacian_local_mixed_source_L2 μ Q measurableSet_ball F.val d w e e
    he hed' ‖q‖₊ M hwb hFgrad q hw hq
  have hsame : (∫ x, q x*(e x)^2 ∂μ)+weightedGamma μ Q e F.val w =
      -(∫ x, q x*localGamma μ Q F.val d x ∂μ) := by
    convert hmix using 1
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hb : (1/(n:ℝ))*(∫ x, q x*(e x)^2 ∂μ)≤bochnerTestForm μ Q (-K) H w -
      ∫ x, q x*localGamma μ Q F.val d x ∂μ := by
    rw [bochnerTestForm_apply]
    linarith only [hboch,hsame]
  have hHG : SobolevSpace.toLp μ Q H =ᵐ[μ.restrict (ball p r)] SobolevSpace.toLp μ Q G := by
    filter_upwards [ae_restrict_of_ae hH,localGamma_pair_congr_ae μ Q hFu hFu,
      ae_restrict_of_ae hG] with x hx hy hz
    exact hx.trans (hy.trans hz.symm)
  rw [bochnerTestForm_congr_on μ Q measurableSet_ball (-K) hHG w q hw hq] at hb
  have hlocal : localGamma μ Q F.val d =ᵐ[μ.restrict (ball p r)] localGamma μ Q u d :=
    localGamma_pair_congr_ae μ Q hFu (EventuallyEq.refl _ _)
  have hint : (∫ x, q x*localGamma μ Q F.val d x ∂μ) =
      ∫ x, q x*localGamma μ Q u d x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hlocal] with x hx
    by_cases hxB : x ∈ ball p r
    · rw [hx hxB]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxB (hq ht)),zero_mul,zero_mul]
  have hsquare : (∫ x, q x*(e x)^2 ∂μ) =
      ∫ x, q x*(SobolevSpace.toLp μ Q d x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hed'] with x hx
    by_cases hxB : x ∈ ball p r
    · rw [hx hxB]
    · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxB (hq ht)),zero_mul,zero_mul]
  rwa [hint,hsquare] at hb

end RegularPointCoordinates

end

end OAI
