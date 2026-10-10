import OAI.Geometry.RCD.Metric.CompactFactorScaledSource
import OAI.Geometry.RCD.Heat.CompactHeatScalingDensity
import OAI.Geometry.RCD.Harmonic.QuadraticRadialGrowth

namespace OAI

/-! # Uniform quadratic lower sources for the actual backward factor

On the first half of the interpolation, the backward heat time stays away
from zero relative to the noise scale. Only the original endpoint density
and its boundedness are used.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
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

theorem backward_source_lower (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ : X → ℝ) (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R : ℝ} (hR : 0 ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1), (t:ℝ) ≤ 1/2 →
      ∀ (Ω : Set X), IsCompact Ω →
      ∃ (v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
        IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
          fun x => (ε k/2)*Real.log (hX.compactHeatFactor hn p ν (D.right k)
            (ε k/4*(1-t))
            (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)) x)) ∧
        ∀ᵐ x ∂(hausdorff n X).restrict Ω, -A*(1+(dist z x)^2) ≤ q x := by
  obtain ⟨C,E,hC,hE,hdata⟩ := hX.compact_heat_factor_scaled_source hn p hK
  let a := Real.exp |K| *(4*C/(1/2:ℝ))
  let b := Real.exp |K| *(16*E/(1/2:ℝ)^2)
  let e := 2*(n:ℝ)*|K| +8*(n:ℝ)/(1/2:ℝ)
  let A := a+2*b*R^2+2*b+e
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have he : 0 ≤ e := by dsimp only [e]; positivity
  refine ⟨A,by dsimp only [A]; positivity,?_⟩
  intro k t ht Ω hΩ
  have hc : 0 < ε k/2 := half_pos (hε k)
  have hc1 : ε k/2 ≤ 1 := by linarith [hε1 k]
  obtain ⟨v,q,hq,hv,hbound⟩ := hdata ν ρ hm hp hB hν (D.right k) (D.right_pos k)
    hc hc1 (by norm_num : (0:ℝ) < 1/2) (by linarith : (1:ℝ)/2 ≤ 1-t)
    (by linarith [t.property.1] : 1-(t:ℝ) ≤ 1) z R hR hT Ω hΩ
  refine ⟨v,q,hq,?_,?_⟩
  · have htime : ε k/2*(1-(t:ℝ))/2 = ε k/4*(1-t) := by ring
    simpa only [htime] using hv
  · filter_upwards [hbound] with x hx
    have hrad := quadratic_radial_growth_bound (R := R) (r := dist z x) ha hb he
    have hid : Real.exp |K| *(4*C/(1/2:ℝ)+16*E*(R+dist z x)^2/(1/2:ℝ)^2)+
        2*(n:ℝ)*|K| +8*(n:ℝ)/(1/2:ℝ) = a+b*(R+dist z x)^2+e := by
      dsimp only [a,b,e]
      ring
    rw [hid] at hx
    change -A*(1+(dist z x)^2) ≤ q x
    dsimp only [A]
    nlinarith [hx.2]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
