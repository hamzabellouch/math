import OAI.Geometry.RCD.Heat.ScaledCompactReferenceBounds

namespace OAI

/-! # Uniform spacetime amplitude under one fixed additive gauge

The gauge is the factor's value at the fixed center and reference time ε.
The bound covers every point and every interior time in a compact cylinder.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem scaled_compact_heat_spacetime_bounded (hK : K≤0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x|≤B)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) (R : ℝ) (hR : 0≤R) (hdist : ∀ a : S, dist z a≤R)
    {δ r : ℝ} (hδ : 0<δ) (hr : 0≤r) :
    ∃ M : ℝ, 0≤M ∧ ∀ (F : C(S, ℝ)), (∀ a, 0<F a) →
      ∀ {ε s : ℝ} (hε : 0<ε), ε≤1 → (hδs : δ≤ s) → s≤1 →
      ∀ x∈closedBall z r,
        |hX.scaledCompactHeatPotential hn p ν F ε s
          (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) x-
          ε*Real.log (hX.compactHeatFactor hn p ν F ε hε z)|≤M := by
  obtain ⟨C,D,hC,hD,hRef⟩ := hX.scaled_compact_heat_reference_bounds hn p hK
  obtain ⟨G,J,hG,hJ,hLip⟩ := hX.compact_heat_factor_scaled_lipschitz hn p
  let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| * (4*G/δ+16*J*(R+8*(r+1))^2/δ^2)),Real.sqrt_nonneg _⟩
  let N := C+2*D*R^2/δ+(n:ℝ)*(2/δ+|K|)
  let M := (L:ℝ)*r+N
  have hN : 0≤N := by dsimp only [N]; positivity
  refine ⟨M,by dsimp only [M]; positivity,?_⟩
  intro F hF ε s hε hε1 hδs hs1 x hx
  let v := fun y => hX.scaledCompactHeatPotential hn p ν F ε s
    (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) y
  let b := ε*Real.log (hX.compactHeatFactor hn p ν F ε hε z)
  have hl : LipschitzOnWith L v (ball z (r+1)) :=
    hLip ν ρ hρ hρ0 hB hν F hF hε hε1 hδ hδs hs1 z R hR hdist (by linarith)
  have hxD : dist x z≤r := mem_closedBall.mp hx
  have hxB : x∈ball z (r+1) := mem_ball.mpr (by linarith)
  have hzB : z∈ball z (r+1) := by rw [mem_ball,dist_self]; linarith
  have hsp : |v x-v z|≤(L:ℝ)*r := by
    have hh := hl.dist_le_mul x hxB z hzB
    rw [Real.dist_eq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hxD L.coe_nonneg)
  have href := hRef ν ρ hρ hρ0 hB hν F hF hε hε1 hδ hδs hs1 z R hR hdist
  change -(C+2*D*R^2/δ)≤v z-b ∧ v z-b≤(n:ℝ)*(2/δ+|K|) at href
  have habs : |v z-b|≤N := by
    apply abs_le.mpr
    dsimp only [N]
    constructor <;> nlinarith [href.1,href.2,show 0≤C+2*D*R^2/δ by positivity,
      show 0≤(n:ℝ)*(2/δ+|K|) by positivity]
  change |v x-b|≤M
  calc
    _ = |(v x-v z)+(v z-b)| := by congr 1; ring
    _ ≤ |v x-v z|+|v z-b| := abs_add_le _ _
    _ ≤ (L:ℝ)*r+N := add_le_add hsp habs

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
