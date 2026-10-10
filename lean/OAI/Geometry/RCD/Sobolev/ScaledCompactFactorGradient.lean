import OAI.Geometry.RCD.Heat.CompactFactorLogGradient
import OAI.Geometry.RCD.Heat.ScaledHamiltonBound

namespace OAI

/-! # Uniform gradients of the actual small-noise logarithmic potentials

Both the potential and its weak source are scaled before taking limits.
The bound is uniform over noise parameters in (0,1] and interior times.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_scaled_gradient :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x|≤B) →
        ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0<F a) →
        ∀ {ε s δ : ℝ} (hε : 0<ε) (_hε1 : ε≤1) (hδ : 0<δ) (hδs : δ≤ s) (_hs1 : s≤1),
        ∀ (z : X) (R : ℝ), 0≤R → (∀ a : S, dist z a≤R) →
        ∀ (Ω : Set X), IsCompact Ω →
        ∃ (v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
          IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
            fun x => ε*Real.log (hX.compactHeatFactor hn p ν F (ε*s/2) (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) x)) ∧
          ∀ᵐ x ∂(hausdorff n X).restrict Ω,
            (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic v x)^2≤
              Real.exp |K| * (4*C/δ+16*D*(R+dist z x)^2/δ^2) := by
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_log_gradient hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε s δ hε hε1 hδ hδs hs1 z R hR hdist Ω hΩ
  let μ := hausdorff n X
  let Q := hX.quadratic
  let t := ε*s/4
  have hs : 0<s := hδ.trans_le hδs
  have ht : 0<t := by dsimp [t]; positivity
  have ht1 : t≤1/2 := by
    have hm := mul_le_mul hε1 hs1 hs.le (by norm_num : (0:ℝ)≤1)
    dsimp only [t]
    linarith only [hm]
  have htime : 2*t=ε*s/2 := by dsimp only [t]; ring
  obtain ⟨v,q,hq,hv,hgrad⟩ := hdata ν ρ hρ hρ0 hB hν F hF t ht ht1 z R hR hdist Ω hΩ
  refine ⟨ε • v,ε • q,hq.smul μ Q ε,?_,?_⟩
  · have hr := Lp.coeFn_smul ε (SobolevSpace.toLp μ Q v)
    filter_upwards [ae_restrict_of_ae hr,hv] with x hx hy
    change SobolevSpace.toLp μ Q (ε • v) x = ε*SobolevSpace.toLp μ Q v x at hx
    rw [hx,hy]
    simp only [htime]
  · have hg : SobolevSpace.minimalSlope μ Q (ε • v) =ᵐ[μ] fun x =>
        ε*SobolevSpace.minimalSlope μ Q v x := by
      rw [SobolevSpace.minimalSlope_smul_nonneg μ Q v hε.le]
      exact Lp.coeFn_smul ε (SobolevSpace.minimalSlope μ Q v)
    filter_upwards [hgrad,ae_restrict_of_ae hg] with x hx hy
    rw [hy]
    exact scaled_hamilton_bound (abs_nonneg K) hC hD.le hε hε1 hδ hδs hs1 rfl hx

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
