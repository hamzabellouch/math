import OAI.Geometry.RCD.Heat.KernelHeatCompactPowerDerivative
import OAI.Geometry.RCD.Metric.CompactFactorL2
import OAI.Geometry.RCD.Heat.CompactHeatScalingData

namespace OAI

/-! # Localized power evolution of the original compact scaling family -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
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

def interpolationPowerMean (Ω : Set X) (q k : ℕ) (s : ℝ) : ℝ :=
  ∫ x in Ω,
    ((∫ a, hX.canonicalHeatKernel hn p (ε k/4*s) x a*D.left k a ∂μ)*
      (∫ b, hX.canonicalHeatKernel hn p (ε k/4*(1-s)) x b*D.right k b ∂ν))^q
      ∂hausdorff n X

theorem interpolationPowerMean_hasDerivAt
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (k : ℕ) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let c := ε k/4
    ∃ f g : Lp ℝ 2 m, HasBoundedAmplitude f ∧ HasBoundedAmplitude g ∧
      ∀ (Ω : Set X), IsCompact Ω → ∀ (q : ℕ) (t : ℝ), 0 < t → t < 1 →
        HasDerivAt (D.interpolationPowerMean Ω q k)
          (c*(q:ℝ)*(∫ x in Ω,
            (kernelHeat m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x)^(q-1)*
              (kernelHeatGeneratorSource m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x-
                kernelHeat m Q hk (c*t) f x*kernelHeatGeneratorSource m Q hk (c-c*t) g x) ∂m)) t := by
  intro m Q hk c
  obtain ⟨f,hf,hfe⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨g,hg,hge⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  refine ⟨f,g,hf,hg,?_⟩
  intro Ω hΩ q t ht ht1
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hs : 0 < c*t := mul_pos hc ht
  have hsc : c*t < c := mul_lt_of_lt_one_right hc ht1
  have hd := (kernelHeat_compact_power_hasDerivAt m Q hk f g hs hsc hΩ q).scomp t
    ((hasDerivAt_id t).const_mul c)
  have hder : HasDerivAt
      (fun s => ∫ x in Ω, (kernelHeat m Q hk (c*s) f x*kernelHeat m Q hk (c-c*s) g x)^q ∂m)
      (c*(q:ℝ)*(∫ x in Ω,
        (kernelHeat m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x)^(q-1)*
          (kernelHeatGeneratorSource m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x-
            kernelHeat m Q hk (c*t) f x*kernelHeatGeneratorSource m Q hk (c-c*t) g x) ∂m)) t := by
    convert hd using 1
    · rfl
    · simp only [smul_eq_mul,mul_one]
      ring
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht1] with s hs
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  have h₁ := hfe (c*s) (mul_pos hc hs.1) x
  have h₂ := hge (c*(1-s)) (mul_pos hc (sub_pos.mpr hs.2)) x
  change (∫ a, hX.canonicalHeatKernel hn p (c*s) x a*D.left k a ∂μ) =
    kernelHeat m Q hk (c*s) f x at h₁
  change (∫ b, hX.canonicalHeatKernel hn p (c*(1-s)) x b*D.right k b ∂ν) =
    kernelHeat m Q hk (c*(1-s)) g x at h₂
  rw [show c*(1-s) = c-c*s by ring] at h₂
  change ((∫ a, hX.canonicalHeatKernel hn p (c*s) x a*D.left k a ∂μ)*
    (∫ b, hX.canonicalHeatKernel hn p (c*(1-s)) x b*D.right k b ∂ν))^q = _
  rw [show c*(1-s) = c-c*s by ring]
  exact congrArg (fun r : ℝ => r^q) (congrArg₂ (· * ·) h₁ h₂)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
