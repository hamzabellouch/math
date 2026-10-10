import OAI.Geometry.RCD.Heat.CompactHeatPowerDerivative
import OAI.Geometry.RCD.Heat.KernelHeatGlobalPowerDerivative
import OAI.Geometry.RCD.Metric.CompactFactorIntegrableEnvelope
import OAI.Geometry.RCD.Heat.BoundedProductPowerIntegrable

namespace OAI

/-! # Global power evolution of the original compact scaling family -/

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

theorem interpolationPowerMean_global_hasDerivAt (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) (k : ℕ) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let c := ε k/4
    ∃ f g : Lp ℝ 2 m, HasBoundedAmplitude f ∧ HasBoundedAmplitude g ∧
      (∀ (s : ℝ) (hs : 0 < s) (x : X),
        hX.compactHeatFactor hn p μ (D.left k) s hs x = kernelHeat m Q hk s f x) ∧
      (∀ (s : ℝ) (hs : 0 < s) (x : X),
        hX.compactHeatFactor hn p ν (D.right k) s hs x = kernelHeat m Q hk s g x) ∧
      ∀ (q : ℕ), 1 ≤ q → ∀ (t : ℝ), 0 < t → t < 1 →
        HasDerivAt (D.interpolationPowerMean univ q k)
          (c*(q:ℝ)*(∫ x in univ,
            (kernelHeat m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x)^(q-1)*
              (kernelHeatGeneratorSource m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x-
                kernelHeat m Q hk (c*t) f x*kernelHeatGeneratorSource m Q hk (c-c*t) g x) ∂m)) t := by
  intro m Q hk c
  obtain ⟨f,A,hf0,hf,hfe⟩ := hX.compact_heat_factor_nonnegative_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ
    (D.left k) (fun a => (D.left_pos k a).le)
  obtain ⟨g,B,hg0,hg,hge⟩ := hX.compact_heat_factor_nonnegative_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν
    (D.right k) (fun b => (D.right_pos k b).le)
  refine ⟨f,g,⟨A,hf⟩,⟨B,hg⟩,hfe,hge,?_⟩
  intro q hq t ht ht1
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hc1 : c ≤ 1 := by dsimp only [c]; linarith [hε1 k]
  let a := c*t/2
  let b := (c*t+c)/2
  have ha : 0 < a := by dsimp only [a]; positivity
  have hct : c*t < c := mul_lt_of_lt_one_right hc ht1
  have hb : b < c := by dsimp only [b]; linarith
  have hab : a ≤ b := by dsimp only [a,b]; linarith
  have hτ : c*t ∈ Ioo a b := by dsimp only [a,b]; constructor <;> nlinarith
  have hca : 0 < c-b := sub_pos.mpr hb
  have hback : c-b ≤ c-a := by linarith
  have hb1 : b ≤ 1 := hb.le.trans hc1
  have hca1 : c-a ≤ 1 := by linarith
  obtain ⟨H₀,hH₀,_hpH₀,hEnv₀⟩ := hX.compact_factor_integrable_envelope hn p μ ρ₀ hm₀ hp₀ hC₀ hμ
    (D.left k) (D.left_pos k) z hR hS ha hab hb1
  obtain ⟨H₁,hH₁,_hpH₁,hEnv₁⟩ := hX.compact_factor_integrable_envelope hn p ν ρ₁ hm₁ hp₁ hC₁ hν
    (D.right k) (D.right_pos k) z hR hT hca hback hca1
  have henv : ∀ r ∈ Ioo a b, ∀ x, kernelHeat m Q hk r f x+kernelHeat m Q hk (c-r) g x ≤
      H₀ x+H₁ x := by
    intro r hr x
    have hr0 : 0 < r := ha.trans hr.1
    have hcr0 : 0 < c-r := sub_pos.mpr (hr.2.trans hb)
    have h₀ := (le_abs_self _).trans (hEnv₀ r hr.1.le hr.2.le x)
    have h₁ := (le_abs_self _).trans (hEnv₁ (c-r) (by linarith [hr.2]) (by linarith [hr.1]) x)
    rw [hfe r hr0 x] at h₀
    rw [hge (c-r) hcr0 x] at h₁
    exact add_le_add h₀ h₁
  have hi : Integrable (fun x => (kernelHeat m Q hk (c*t) f x*
      kernelHeat m Q hk (c-c*t) g x)^q) m := by
    have hct0 := mul_pos hc ht
    have hback0 := sub_pos.mpr hct
    have hfm : MemLp (kernelHeat m Q hk (c*t) f) 2 m :=
      (memLp_congr_ae (kernelHeat_represents_L2 m Q hk hct0 f)).mpr (Lp.memLp _)
    have hgm : MemLp (kernelHeat m Q hk (c-c*t) g) 2 m :=
      (memLp_congr_ae (kernelHeat_represents_L2 m Q hk hback0 g)).mpr (Lp.memLp _)
    exact bounded_product_power_integrable hfm hgm
      (Eventually.of_forall (hX.kernelHeat_bounded_regularity hn p hk f A hf _ hct0).2)
      (Eventually.of_forall (hX.kernelHeat_bounded_regularity hn p hk g B hg _ hback0).2)
      A.coe_nonneg B.coe_nonneg hq
  have hd := (hX.kernelHeat_global_power_hasDerivAt hn p hK hk f g hf0 hg0 A B hf hg
    ha hb hτ (fun x => H₀ x+H₁ x) (hH₀.add hH₁) henv q hi).scomp t
    ((hasDerivAt_id t).const_mul c)
  have hder : HasDerivAt
      (fun s => ∫ x in univ, (kernelHeat m Q hk (c*s) f x*kernelHeat m Q hk (c-c*s) g x)^q ∂m)
      (c*(q:ℝ)*(∫ x in univ,
        (kernelHeat m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x)^(q-1)*
          (kernelHeatGeneratorSource m Q hk (c*t) f x*kernelHeat m Q hk (c-c*t) g x-
            kernelHeat m Q hk (c*t) f x*kernelHeatGeneratorSource m Q hk (c-c*t) g x) ∂m)) t := by
    simpa only [setIntegral_univ,Function.comp_def,smul_eq_mul,mul_one,one_mul,
      mul_assoc,mul_comm,mul_left_comm] using hd
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
