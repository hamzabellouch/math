import OAI.Geometry.RCD.Heat.LocalizedOsmoticNoiseRate
import OAI.Geometry.RCD.Heat.HeatLocalOsmoticEstimate
import OAI.Geometry.RCD.Heat.BoundedHeatMixedGramBounds

namespace OAI

/-! # Explicit local osmotic decay for the actual RCD heat evolution

Only values and local gradient bounds of the logarithmic representatives
are required. Their mixed chain rules and the energy inequality are proved
from the original heat data.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heat_osmotic_noise_rate (hK : K≤0)
    (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0) (hf0 : 0≤f) (hg0 : 0≤g)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hg : ∀ᵐ x ∂hausdorff n X, |g x|≤B)
    {c δ a b : ℝ} (hc : 0<c) (hc1 : c≤1) (hδ : 0<δ) (ha : δ≤a) (hb : δ≤b)
    (φ : X → ℝ) (M : ℝ≥0) (hφ : LipschitzWith M φ) (hφs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1)
    (U V : SobolevSpace (hausdorff n X) hX.quadratic)
    {Lv Lo : ℝ} (hLo : 0≤Lo) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let F := kernelHeat m Q hk (c*a) f
    let G := kernelHeat m Q hk (c*b) g
    (∀ x, 0<F x) → (∀ x, 0<G x) →
    IsProbabilityMeasure (m.withDensity (fun x => ENNReal.ofReal (F x*G x))) →
    (SobolevSpace.toLp m Q U =ᵐ[m.restrict (tsupport φ)] fun x => Real.log (F x)) →
    (SobolevSpace.toLp m Q V =ᵐ[m.restrict (tsupport φ)] fun x => Real.log (G x)) →
    (∀ᵐ x ∂m.restrict (tsupport φ), SobolevSpace.minimalSlope m Q (c • (V-U)) x≤Lv) →
    (∀ᵐ x ∂m.restrict (tsupport φ), SobolevSpace.minimalSlope m Q (c • (U+V)) x≤Lo) →
    weightedGamma m Q (fun x => φ x*(F x*G x)) (c • (U+V)) (c • (U+V)) ≤
      c*(Lv^2+4*(n:ℝ)*|K|+4*(n:ℝ)/δ+2*(Lo*M)) := by
  intro m Q hk F G hFpos hGpos hprob hU hV hvel hosm
  have : IsProbabilityMeasure (m.withDensity (fun x => ENNReal.ofReal (F x*G x))) := hprob
  have hs := mul_pos hc (hδ.trans_le ha)
  have ht := mul_pos hc (hδ.trans_le hb)
  let u := heatSobolev m Q (c*a) hs f
  let v := heatSobolev m Q (c*b) ht g
  let w := SobolevSpace.ofLipschitzCompact m Q hφ hφs
  have hu : SobolevSpace.toLp m Q u =ᵐ[m] F := by
    simpa only [u,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk hs f).symm
  have hv : SobolevSpace.toLp m Q v =ᵐ[m] G := by
    simpa only [v,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk ht g).symm
  obtain ⟨a₀,a₁,ha₀,ha₁,hua⟩ := hX.bounded_heat_positive_range hn p f A hf hs
    hφs (fun x _ => hFpos x)
  obtain ⟨b₀,b₁,hb₀,hb₁,hvb⟩ := hX.bounded_heat_positive_range hn p g B hg ht
    hφs (fun x _ => hGpos x)
  have hU' : SobolevSpace.toLp m Q U =ᵐ[m.restrict (tsupport φ)]
      fun x => Real.log (SobolevSpace.toLp m Q u x) := by
    filter_upwards [hU,ae_restrict_of_ae hu] with x hx hy
    rw [hx,hy]
  have hV' : SobolevSpace.toLp m Q V =ᵐ[m.restrict (tsupport φ)]
      fun x => Real.log (SobolevSpace.toLp m Q v x) := by
    filter_upwards [hV,ae_restrict_of_ae hv] with x hx hy
    rw [hx,hy]
  have hCU (z : SobolevSpace m Q) : localGamma m Q U z =ᵐ[m.restrict (tsupport φ)]
      fun x => localGamma m Q u z x/F x := by
    filter_upwards [local_logarithm_gamma_of_value m Q u U ha₀ ha₁ hua hU' z,
      ae_restrict_of_ae hu] with x hx hy
    rwa [hy] at hx
  have hCV (z : SobolevSpace m Q) : localGamma m Q V z =ᵐ[m.restrict (tsupport φ)]
      fun x => localGamma m Q v z x/G x := by
    filter_upwards [local_logarithm_gamma_of_value m Q v V hb₀ hb₁ hvb hV' z,
      ae_restrict_of_ae hv] with x hx hy
    rwa [hy] at hx
  have hFc : Continuous F := kernelHeat_continuous m Q hk hs f
  have hGc : Continuous G := kernelHeat_continuous m Q hk ht g
  have hFB := (hX.kernelHeat_bounded_regularity hn p hk f A hf (c*a) hs).2
  have hGB := (hX.kernelHeat_bounded_regularity hn p hk g B hg (c*b) ht).2
  have hiu := compact_ratio_weight_integrable m φ F G (localGamma m Q u u)
    hφ.continuous hφs hFc (fun x _ => hFpos x) hGc.measurable.aestronglyMeasurable
    (Eventually.of_forall hGB) (localGamma_memL1 m Q u u)
  have hiv := compact_ratio_weight_integrable m φ G F (localGamma m Q v v)
    hφ.continuous hφs hGc (fun x _ => hGpos x) hFc.measurable.aestronglyMeasurable
    (Eventually.of_forall hFB) (localGamma_memL1 m Q v v)
  have hie : Integrable (fun x => φ x*localGamma m Q u v x) m := by
    simpa only [Pi.mul_apply] using (localGamma_memL1 m Q u v).bdd_mul
      hφ.continuous.measurable.aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hφ01 x).1]; exact (hφ01 x).2)
  have hw := SobolevSpace.ofLipschitzCompact_coe m Q hφ hφs
  have hw0 : ∀ᵐ x ∂m, x ∉ tsupport φ → SobolevSpace.toLp m Q w x=0 := by
    filter_upwards [hw] with x hx hxs
    exact hx.trans (image_eq_zero_of_notMem_tsupport hxs)
  have he := hX.heat_local_osmotic_estimate hn p hK (1+c) (by linarith) f g A B
    hf0 hg0 hf hg hs ht φ M hφ hφs (fun x => (hφ01 x).1)
    (fun x _ => hFpos x) (fun x _ => hGpos x)
  dsimp only at he
  have hsub : 1+c-1=c := by ring
  have hadd : 1+c+1=2+c := by ring
  have hmass : (∫ x, φ x*G x*F x ∂m) = ∫ x, φ x*(F x*G x) ∂m :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [hsub,hadd,hmass] at he
  exact localized_osmotic_noise_rate m Q (isClosed_tsupport φ).measurableSet φ F G hφ01
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx) hFc.measurable hGc.measurable
    (fun x => (hFpos x).le) (fun x => (hGpos x).le)
    (fun x _ => hFpos x) (fun x _ => hGpos x)
    (Eventually.of_forall hFB) (Eventually.of_forall hGB) u v U V w hCU hCV hiu hiv hie
    hc hc1 hδ ha hb (Nat.cast_nonneg n) (abs_nonneg K) hLo M.coe_nonneg hvel hosm
    (SobolevSpace.ofLipschitzCompact_minimalSlope_le_lip m Q hφ hφs) hw0 he

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
