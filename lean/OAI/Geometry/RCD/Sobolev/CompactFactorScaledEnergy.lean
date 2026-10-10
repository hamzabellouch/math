import OAI.Geometry.RCD.Sobolev.ScaledCompactFactorGradient
import OAI.Geometry.RCD.Heat.ScaledLogarithmSelfGamma
import OAI.Geometry.RCD.Heat.BoundedHeatMixedGramBounds
import OAI.Geometry.RCD.Metric.CompactFactorL2

namespace OAI

/-! # Quantitative energy of the original compact heat factors

The coefficient is independent of the scaling function, noise and compact
region. No derivative of a logarithmic extension remains in the conclusion.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem compact_factor_scaled_energy :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 < D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) →
        ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S,ℝ)), (∀ y, 0 < F y) →
        ∀ {ε s δ : ℝ} (hε : 0 < ε), ε ≤ 1 → (hδ : 0 < δ) → (hδs : δ ≤ s) → s ≤ 1 →
        ∀ (z : X) (R : ℝ), 0 ≤ R → (∀ y : S, dist z y ≤ R) →
        ∀ (Ω : Set X), IsCompact Ω →
        ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X]
            hX.compactHeatFactor hn p ν F (ε*s/2)
              (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num))) →
          ∀ᵐ x ∂(hausdorff n X).restrict Ω,
            ε^2*localGamma (hausdorff n X) hX.quadratic u u x ≤
              (SobolevSpace.toLp (hausdorff n X) hX.quadratic u x)^2*
                (Real.exp |K| *(4*C/δ+16*D*(R+dist z x)^2/δ^2)) := by
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_scaled_gradient hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε s δ hε hε1 hδ hδs hs1 z R hR hdist Ω hΩ u hu
  let μ := hausdorff n X
  let Q := hX.quadratic
  have ht : 0 < ε*s/2 := div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)
  obtain ⟨P,q,_hq,hP,hgrad⟩ := hdata ν ρ hρ hρ0 hB hν F hF hε hε1 hδ hδs hs1 z R hR hdist Ω hΩ
  obtain ⟨f,⟨A,hA⟩,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hB hν F
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hpos (x : X) (_hx : x ∈ Ω) : 0 < kernelHeat μ Q hk (ε*s/2) f x := by
    rw [← he _ ht x]
    exact hX.compactHeatFactor_positive hn p ν F hF _ ht x
  have heq : u=heatSobolev μ Q (ε*s/2) ht f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hu,kernelHeat_represents_L2 μ Q hk ht f] with x hx hy
    exact hx.trans ((he _ ht x).trans hy)
  obtain ⟨a,b,ha,hab,hrange⟩ := hX.bounded_heat_positive_range hn p f A hA ht hΩ hpos
  have hurange : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a b := by
    rw [heq]
    exact hrange
  have hlog : SobolevSpace.toLp μ Q P =ᵐ[μ.restrict Ω]
      fun x => ε*Real.log (SobolevSpace.toLp μ Q u x) := by
    filter_upwards [hP,ae_restrict_of_ae hu] with x hx hy
    rw [hy]
    exact hx
  have henergy := scaled_logarithm_self_gamma μ Q u P ha hab hε hurange hlog
  filter_upwards [henergy,hgrad,ae_restrict_of_ae (localGamma_self μ Q P)] with x hx hg hs
  rw [hx,hs]
  exact mul_le_mul_of_nonneg_left hg (sq_nonneg _)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
