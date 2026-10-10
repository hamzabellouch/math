import OAI.Geometry.RCD.Sobolev.ScaledCompactFactorLipschitz
import OAI.Geometry.RCD.Metric.CenteredBallCompactness

namespace OAI

/-! # Spatial compactness of the actual normalized entropic potentials

Endpoint scaling functions and interior times may vary along the sequence.
Only the common support, noise range and interior-time margin enter the
uniform Lipschitz bound. This is spatial compactness; no identification
with a transport potential or time convergence is asserted here.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

def scaledCompactHeatPotential {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : C(S, ℝ)) (ε s : ℝ)
    (ht : 0<ε*s/2) (x : X) : ℝ :=
  ε*Real.log (hX.compactHeatFactor hn p ν F (ε*s/2) ht x)

theorem compact_heat_factor_centered_compactness {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x|≤B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : ℕ → C(S, ℝ)) (hF : ∀ k a, 0<F k a)
    (ε s : ℕ → ℝ) (hε : ∀ k, 0<ε k) (hε1 : ∀ k, ε k≤1)
    {δ : ℝ} (hδ : 0<δ) (hδs : ∀ k, δ≤ s k) (hs1 : ∀ k, s k≤1)
    (z : X) {R r : ℝ} (hR : 0≤R) (hdist : ∀ a : S, dist z a≤R) (hr : 0<r) :
    ∃ (L : ℝ≥0) (g : closedBall z r → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      LipschitzWith L g ∧ g ⟨z,mem_closedBall_self hr.le⟩=0 ∧
      TendstoUniformly (fun k (x : closedBall z r) =>
        hX.scaledCompactHeatPotential hn p ν (F (a k)) (ε (a k)) (s (a k))
          (div_pos (mul_pos (hε _) (hδ.trans_le (hδs _))) (by norm_num)) x-
        hX.scaledCompactHeatPotential hn p ν (F (a k)) (ε (a k)) (s (a k))
          (div_pos (mul_pos (hε _) (hδ.trans_le (hδs _))) (by norm_num)) z) g atTop := by
  obtain ⟨C,D,_hC,_hD,hdata⟩ := hX.compact_heat_factor_scaled_lipschitz hn p
  let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| * (4*C/δ+16*D*(R+8*(r+1))^2/δ^2)),Real.sqrt_nonneg _⟩
  let u := fun k => hX.scaledCompactHeatPotential hn p ν (F k) (ε k) (s k)
    (div_pos (mul_pos (hε k) (hδ.trans_le (hδs k))) (by norm_num))
  have hu (k : ℕ) : LipschitzOnWith L (u k) (ball z (r+1)) :=
    hdata ν ρ hρ hρ0 hB hν (F k) (hF k) (hε k) (hε1 k) hδ (hδs k) (hs1 k)
      z R hR hdist (by linarith)
  obtain ⟨g,a,ha,hg,hg0,hlim⟩ := centered_ball_subsequence z hr u L hu
  exact ⟨L,g,a,ha,hg,hg0,hlim⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
