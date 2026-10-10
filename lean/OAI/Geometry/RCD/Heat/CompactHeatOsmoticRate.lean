import OAI.Geometry.RCD.Heat.CompactScaledLogBound
import OAI.Geometry.RCD.Metric.CompactFactorNonnegativeL2
import OAI.Geometry.RCD.Heat.HeatOsmoticNoiseRate
import OAI.Geometry.RCD.Heat.ScaledLogPairBounds
import OAI.Geometry.RCD.Heat.CompactHeatScalingDensity

namespace OAI

/-! # Uniform local osmotic decay of the original compact scaling sequence -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem local_osmotic_rate (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ a : T, dist z a ≤ R) (hδ : 0 < δ)
    (φ : X → ℝ) (M : ℝ≥0) (hφ : LipschitzWith M φ) (hφs : HasCompactSupport φ)
    (hφ01 : ∀ x, φ x ∈ Icc (0:ℝ) 1) (hsupp : tsupport φ ⊆ closedBall z r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1), δ ≤ t → δ ≤ 1-t →
      ∃ η : SobolevSpace (hausdorff n X) hX.quadratic,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic η
          =ᵐ[(hausdorff n X).restrict (tsupport φ)] fun x => (ε k/4)*
            (Real.log (hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t)
              (mul_pos (div_pos (hε k) (by norm_num)) t.property.1) x)+
             Real.log (hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t))
              (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)) x))) ∧
        weightedGamma (hausdorff n X) hX.quadratic
          (fun x => φ x*D.interpolationDensity k t x) η η ≤ (ε k/4)*C := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨H₀,hH₀,hleft⟩ := hX.compact_scaled_log_uniform_bound hn p μ ρ₀ hm₀ hp₀ hC₀ hμ z hR hS hδ (r := r)
  obtain ⟨H₁,hH₁,hright⟩ := hX.compact_scaled_log_uniform_bound hn p ν ρ₁ hm₁ hp₁ hC₁ hν z hR hT hδ (r := r)
  let H := max H₀ H₁
  have hH : 0 ≤ H := hH₀.trans (le_max_left _ _)
  let L := Real.sqrt H
  let C := L^2+4*(n:ℝ)*|K| +4*(n:ℝ)/δ+2*(L*M)
  refine ⟨C,by dsimp only [C,L]; positivity,?_⟩
  intro k t hδt hδt'
  let c := ε k/4
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hc2 : 2*c ≤ 1 := by dsimp only [c]; linarith [hε1 k]
  have hc1 : c ≤ 1 := by linarith
  have hs : 0 < c*(t:ℝ) := mul_pos hc t.property.1
  have ht : 0 < c*(1-t) := mul_pos hc (sub_pos.mpr t.property.2)
  let F := hX.compactHeatFactor hn p μ (D.left k) (c*t) hs
  let G := hX.compactHeatFactor hn p ν (D.right k) (c*(1-t)) ht
  obtain ⟨P,hP,hPg⟩ := hleft (D.left k) (D.left_pos k) hc hc2 hδt t.property.2.le
  obtain ⟨V,hV,hVg⟩ := hright (D.right k) (D.right_pos k) hc hc2 hδt' (by linarith [t.property.1])
  have hPg' : ∀ᵐ x ∂m.restrict (closedBall z r), (SobolevSpace.minimalSlope m Q P x)^2 ≤ H :=
    hPg.mono fun _ hx => hx.trans (le_max_left _ _)
  have hVg' : ∀ᵐ x ∂m.restrict (closedBall z r), (SobolevSpace.minimalSlope m Q V x)^2 ≤ H :=
    hVg.mono fun _ hx => hx.trans (le_max_right _ _)
  obtain ⟨U,W,hU,hW,hvel,hosm⟩ := scaled_log_pair_bounds m Q F G P V hc hH hP hV hPg' hVg'
  have hU' := ae_restrict_of_ae_restrict_of_subset hsupp hU
  have hW' := ae_restrict_of_ae_restrict_of_subset hsupp hW
  have hvel' := ae_restrict_of_ae_restrict_of_subset hsupp hvel
  have hosm' := ae_restrict_of_ae_restrict_of_subset hsupp hosm
  obtain ⟨f,A,hf0,hf,hef⟩ := hX.compact_heat_factor_nonnegative_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ
    (D.left k) (fun a => (D.left_pos k a).le)
  obtain ⟨g,B,hg0,hg,heg⟩ := hX.compact_heat_factor_nonnegative_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν
    (D.right k) (fun a => (D.right_pos k a).le)
  have hFe : ∀ x, F x=kernelHeat m Q hk (c*t) f x := hef _ hs
  have hGe : ∀ x, G x=kernelHeat m Q hk (c*(1-t)) g x := heg _ ht
  have hFd : F = kernelHeat m Q hk (c*t) f := funext hFe
  have hGd : G = kernelHeat m Q hk (c*(1-t)) g := funext hGe
  have hden : (fun x => F x*G x)=D.interpolationDensity k t := rfl
  have hprob : IsProbabilityMeasure (m.withDensity (fun x => ENNReal.ofReal
      (kernelHeat m Q hk (c*t) f x*kernelHeat m Q hk (c*(1-t)) g x))) := by
    rw [← hFd,← hGd]
    exact D.interpolationDensity_probability k t
  have hbound := hX.heat_osmotic_noise_rate hn p hK f g A B hf0 hg0 hf hg
    hc hc1 hδ hδt hδt' φ M hφ hφs hφ01 U W (Real.sqrt_nonneg H)
    (fun x => (hFe x) ▸ hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ hs x)
    (fun x => (hGe x) ▸ hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ ht x)
    hprob (hFd ▸ hU') (hGd ▸ hW') hvel' hosm'
  refine ⟨c • (U+W),?_,?_⟩
  · filter_upwards [hU',hW',ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp m Q U) (SobolevSpace.toLp m Q W)),
      ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp m Q (U+W)))] with x hu hw ha hm
    have ha' : SobolevSpace.toLp m Q (U+W) x =
        SobolevSpace.toLp m Q U x+SobolevSpace.toLp m Q W x := by
      simpa only [map_add,Pi.add_apply] using ha
    change SobolevSpace.toLp m Q (c • (U+W)) x=c*SobolevSpace.toLp m Q (U+W) x at hm
    change SobolevSpace.toLp m Q (c • (U+W)) x=c*(Real.log (F x)+Real.log (G x))
    rw [hm,ha',hu,hw]
  · change weightedGamma m Q (fun x => φ x*(F x*G x)) (c • (U+W)) (c • (U+W)) ≤ c*C
    rw [hFd,hGd]
    exact hbound

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
