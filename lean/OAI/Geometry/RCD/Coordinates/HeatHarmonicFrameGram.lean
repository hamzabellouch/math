import OAI.Geometry.RCD.Heat.HeatMixedGramEnergy
import OAI.Geometry.RCD.Sobolev.HarmonicCoreBochnerMeasure

namespace OAI

/-! # One heat Bochner measure for the whole original harmonic frame -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_harmonic_frame_gram_data {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : X) (U : Fin n → compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Fin n → Lp ℝ 2 (hausdorff n X))
    (hq : ∀ i, IsWeakLaplacian (hausdorff n X) hX.quadratic (U i).val (q i))
    {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (htr : t < 2*r)
    (hq0 : ∀ i, q i =ᵐ[(hausdorff n X).restrict (ball p (2*r))] fun _ => 0)
    (hU : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic (U i).val (U i).val x≤4)
    (h : Lp ℝ 2 (hausdorff n X)) (A Ca : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |h x|≤A)
    (hCa : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic s hs h)
        (heatSobolev (hausdorff n X) hX.quadratic s hs h) x≤(Ca:ℝ)^2) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev μ Q s hs h
    let d := heatSobolevMap μ Q (s/2) (half_pos hs) (-heatGeneratorAt μ Q (s-s/2) h)
    ∃ (F : Fin n → SobolevSpace μ Q) (σ : Fin n → Measure X)
      (H : SobolevSpace μ Q) (τ : Measure X)
      (hσ : ∀ i, IsFiniteMeasure (σ i)) (hτ : IsFiniteMeasure τ),
      letI (i : Fin n) := hσ i
      letI := hτ
      ∃ G : Fin n → SobolevSpace μ Q,
        (∀ i, (SobolevSpace.toLp μ Q (F i) =ᵐ[μ] localGamma μ Q (U i).val (U i).val) ∧
          IsMeasureLaplacianOn μ Q (ball p (2*r)) (F i)
            (bochnerGramSource μ Q K (U i).val (U i).val 0 0 (σ i).toSignedMeasure)) ∧
        (SobolevSpace.toLp μ Q H =ᵐ[μ] localGamma μ Q w w) ∧
        IsMeasureLaplacianOn μ Q (ball p (2*r)) H (bochnerGramSource μ Q K w w d d τ.toSignedMeasure) ∧
        ∀ i, (SobolevSpace.toLp μ Q (G i) =ᵐ[μ.restrict (ball p (2*r))] localGamma μ Q (U i).val w) ∧
          (∫ x in ball p t, localGamma μ Q (G i) (G i) x ∂μ)≤
            2*(Ca:ℝ)^2*(σ i).real (ball p t)+8*τ.real (ball p t) := by
  intro μ Q w d
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  choose F σ hσ hF hFsource using fun i =>
    hX.harmonic_core_bochner_measure hn (U i) (q i) (hq i) p (show 0 < 2*r by linarith) (hq0 i)
  let (i : Fin n) : IsFiniteMeasure (σ i) := hσ i
  obtain ⟨H,τ,hτ,hH,hτsource⟩ := hX.bounded_heat_full_source hn hK p h A hA hs hr
  let := hτ
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,_⟩ := hX.kernelHeat_bounded_regularity hn p hk h A hA s hs
  have hw : SobolevSpace.toLp μ Q w =ᵐ[μ] kernelHeat μ Q hk s h := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q hk hs h).symm
  have hWA := (hX.bounded_heat_sobolev_data hn p h A hA hs).1
  have hd : IsWeakLaplacian μ Q w (SobolevSpace.toLp μ Q d) := heatTail_weak_laplacian μ Q s hs h
  have hdt : SobolevSpace.toLp μ Q d = -heatGeneratorAt μ Q s h :=
    heatTail_deriv_toLp μ Q (s/2) (half_pos hs) h s (by linarith)
  let B : ℝ≥0 := ⟨(2*(n:ℝ)*(|K|+1/s))*(A:ℝ),by positivity⟩
  have hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q d x|≤B := by
    rw [hdt]
    filter_upwards [hX.heatGeneratorAt_amplitude hn p hK h A hA hs,
      Lp.coeFn_neg (heatGeneratorAt μ Q s h)] with x hx he
    rw [he]
    change |-heatGeneratorAt μ Q s h x|≤(2*(n:ℝ)*(|K|+1/s))*(A:ℝ)
    simpa only [abs_neg] using hx
  have hUi (i : Fin n) : ∀ᵐ x ∂μ.restrict (ball p t), localGamma μ Q (U i).val (U i).val x≤(2:ℝ≥0)^2 := by
    simpa only [NNReal.coe_ofNat,show (2:ℝ)^2=4 by norm_num] using hU i
  choose G hG henergy using fun i => hX.bounded_regular_gram_energy hn hK (U i) (q i) (hq i)
    w d hd (kernelHeat μ Q hk s h) hLip hw hWA hB p hr ht htr (hq0 i) (F i) H (σ i) τ
    (ae_restrict_of_ae (hF i)) (ae_restrict_of_ae hH) (hFsource i) hτsource 2 Ca (hUi i) hCa
  refine ⟨F,σ,H,τ,hσ,hτ,G,fun i => ⟨hF i,hFsource i⟩,hH,hτsource,?_⟩
  intro i
  refine ⟨hG i,?_⟩
  simpa only [NNReal.coe_ofNat,show (2:ℝ)*2^2=8 by norm_num] using henergy i

end RegularPointCoordinates

end

end OAI
