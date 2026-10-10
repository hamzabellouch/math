import OAI.Geometry.RCD.Coordinates.HeatHarmonicFrameGram
import OAI.Geometry.RCD.Heat.HeatFullMassBound

namespace OAI

/-! # Quantitative mixed coefficient energy for the actual harmonic frame -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_frame_gram_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p : X) {r s C : ℝ} (hr : 0 < r) (hs : 0 < s) (hC : 0 ≤ C)
    (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic p r C)
    (U : Fin n → compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Fin n → Lp ℝ 2 (hausdorff n X))
    (hq : ∀ i, IsWeakLaplacian (hausdorff n X) hX.quadratic (U i).val (q i))
    (hq0 : ∀ i, q i =ᵐ[(hausdorff n X).restrict (ball p (4*r))] fun _ => 0)
    (hU : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
      localGamma (hausdorff n X) hX.quadratic (U i).val (U i).val x≤4)
    (h : Lp ℝ 2 (hausdorff n X)) (V : X → ℝ) (L A : ℝ≥0)
    (hV : LipschitzWith L V) (hVc : HasCompactSupport V)
    (hrep : V =ᵐ[hausdorff n X] h) (hA : ∀ᵐ x ∂hausdorff n X, |h x|≤A) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev μ Q s hs h
    let ℓ := (L:ℝ)*Real.exp (-K*s)
    let b := (2*(n:ℝ)*(|K|+1/s))*(A:ℝ)
    let m := μ.real (closedBall p (2*r))
    let e i := ∫ x in closedBall p (2*r), |localGamma μ Q (U i).val (U i).val x-1| ∂μ
    ∃ G : Fin n → SobolevSpace μ Q,
      (∀ i, SobolevSpace.toLp μ Q (G i) =ᵐ[μ.restrict (ball p (4*r))] localGamma μ Q (U i).val w) ∧
      ∀ i, (∫ x in ball p r, localGamma μ Q (G i) (G i) x ∂μ)≤
        2*ℓ^2*((C/r^2)/2*e i+(-K)*(e i+m))+
        8*((C/r^2)/2*ℓ^2+(-K)*ℓ^2+b^2+b*ℓ*(C/r))*m := by
  intro μ Q w ℓ b m e
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let L' : ℝ≥0 := ⟨ℓ,mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
  have hw : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q w x≤L' :=
    hX.heat_compact_slope_bdd K n hn hV hVc p h hrep s hs
  have hwg : ∀ᵐ x ∂μ.restrict (ball p r), localGamma μ Q w w x≤(L':ℝ)^2 := by
    filter_upwards [ae_restrict_of_ae hw,ae_restrict_of_ae (localGamma_self μ Q w),
      ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q w))]
      with x hx he hn
    rw [he]
    exact pow_le_pow_left₀ hn hx 2
  have hq0' (i : Fin n) : q i =ᵐ[μ.restrict (ball p (2*(2*r)))] fun _ => 0 := by
    simpa only [show 2*(2*r)=4*r by ring] using hq0 i
  obtain ⟨F,σ,H,τ,hσ,hτ,G,hF,hH,hτs,hG⟩ := hX.heat_harmonic_frame_gram_data hn hK p U q hq
    (show 0<2*r by linarith) hs hr (by linarith) hq0' hU h A L' hA hwg
  let (i : Fin n) : IsFiniteMeasure (σ i) := hσ i
  let : IsFiniteMeasure τ := hτ
  have hΩ : tsupport (χ.weight : X → ℝ) ⊆ ball p (2*(2*r)) :=
    (χ.tsupport_subset μ Q).trans (closedBall_subset_ball (by linarith))
  have hmass (i : Fin n) : (σ i).real (ball p r) ≤ (C/r^2)/2*e i+(-K)*(e i+m) := by
    simpa only [one_mul] using χ.harmonic_full_mass_bound μ Q hr hC hK
      (U i).val (F i) (hF i).1 hΩ (σ i) (hF i).2 1
  have hheat : τ.real (ball p r) ≤
      ((C/r^2)/2*ℓ^2+(-K)*ℓ^2+b^2+b*ℓ*(C/r))*m :=
    hX.heat_full_mass_bound hn hK p hr hs hC χ h V L A hV hVc hrep hA H hH hΩ τ hτs
  refine ⟨G,?_,?_⟩
  · intro i
    simpa only [show 2*(2*r)=4*r by ring] using (hG i).1
  · intro i
    apply (hG i).2.trans
    exact add_le_add (mul_le_mul_of_nonneg_left (hmass i) (by positivity))
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hheat (by norm_num : (0:ℝ)≤8))

end RegularPointCoordinates

end

end OAI
