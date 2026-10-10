import OAI.Geometry.RCD.Heat.ScaledNoiseLipschitz
import OAI.Geometry.RCD.Heat.ScaledHeatActionLimit

namespace OAI

/-! # The limiting heat action has a Lipschitz bound at its physical scale -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem small_noise_action_lipschitz :
    ∃ D : ℝ, 0 < D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (ρ : X → ℝ) (_hρ : Measurable ρ) (_hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0},
      (∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) →
      ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
      ∀ (F : ℕ → C(S,ℝ)), (∀ k y, 0 < F k y) →
      ∀ (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k), (∀ k, ε k ≤ 1) →
      Tendsto ε atTop (𝓝 0) →
      ∀ (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ), Tendsto ι atTop atTop →
      hX.CompactHeatConverges hn p ν F ε hε z ι H →
      ∀ {R r δ : ℝ}, 0 ≤ R → (∀ y:S, dist z y ≤ R) → 0 < r → 0 < δ →
      ∀ t∈Ioo δ 1,
      LipschitzOnWith ⟨Real.sqrt (Real.exp |K| *(16*D*(R+16*r)^2/δ^2)),Real.sqrt_nonneg _⟩
        (H t) (closedBall z r) := by
  obtain ⟨C,D,_hC,hD,hLip⟩ := hX.compact_heat_factor_noise_lipschitz hn p
  refine ⟨D,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε hε hε1 hε0 z ι H hι hconv R r δ hR hdist hr hδ t ht
  let M := Real.exp |K| *(16*D*(R+16*r)^2/δ^2)
  have hL : Tendsto (fun k => Real.sqrt (Real.exp |K| *
      (4*C*ε (ι k)/δ+16*D*(R+16*r)^2/δ^2))) atTop (𝓝 (Real.sqrt M)) := by
    have hh := (((((hε0.comp hι).const_mul (4*C)).div_const δ).add_const
      (16*D*(R+16*r)^2/δ^2)).const_mul (Real.exp |K|)).sqrt
    simpa only [mul_zero,zero_div,zero_add,M,Function.comp_apply] using hh
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hpx := (hconv r hr.le δ hδ t ht).tendsto_at ⟨x,hx⟩
  have hpy := (hconv r hr.le δ hδ t ht).tendsto_at ⟨y,hy⟩
  have hb (k : ℕ) : dist
      (hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t x)
      (hX.fixedGaugeScaledPotential hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z t y) ≤
      Real.sqrt (Real.exp |K| *(4*C*ε (ι k)/δ+16*D*(R+16*r)^2/δ^2))*dist x y := by
    rw [hX.fixedGaugeScaledPotential_eq hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z ht.1.le x,
      hX.fixedGaugeScaledPotential_eq hn p ν (F (ι k)) (ε (ι k)) (hε (ι k)) δ hδ z ht.1.le y,
      dist_sub_right]
    have hh := hLip ν ρ hρ hρ0 hB hν (F (ι k)) (hF (ι k)) (hε (ι k)) (hε1 (ι k)) hδ
      ht.1.le ht.2.le z R hR hdist (r:=2*r) (by positivity)
    have hxb : x∈ball z (2*r) := (show dist x z ≤ r from hx).trans_lt (by linarith)
    have hyb : y∈ball z (2*r) := (show dist y z ≤ r from hy).trans_lt (by linarith)
    have hk := hh.dist_le_mul x hxb y hyb
    change dist _ _ ≤ Real.sqrt (Real.exp |K| *
      (4*C*ε (ι k)/δ+16*D*(R+8*(2*r))^2/δ^2))*dist x y at hk
    rw [show R+8*(2*r)=R+16*r by ring] at hk
    exact hk
  exact le_of_tendsto_of_tendsto (hpx.dist hpy) (hL.mul_const (dist x y)) (Eventually.of_forall hb)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
