import OAI.Geometry.RCD.Heat.PairedHeatActionLimits
import OAI.Geometry.RCD.Heat.ScalingBoundaryLimit
import OAI.Geometry.RCD.Heat.CompactHeatInterpolation

namespace OAI

/-! # The actual compact scaling pair and its two action limits

The kernel has physical time ε/4. Its endpoint normalizations therefore
occur at the interior time 1/2 of the scaled heat potentials. Both
normalized endpoint logarithms converge uniformly on their supports.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_scaling_action_limits (hK : K ≤ 0)
    {S T : Set X} [CompactSpace S] [CompactSpace T] (hS : S.Nonempty) (hT : T.Nonempty)
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ σ : X → ℝ) (hρ : Measurable ρ) (hσ : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x) {B D : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) (hD : ∀ᵐ x ∂hausdorff n X, |σ x| ≤ D)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (σ x)))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hε0 : Tendsto ε atTop (𝓝 0)) (z : X) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist z a ≤ R) (hdT : ∀ b : T, dist z b ≤ R) :
    ∃ (F : ℕ → C(S, ℝ)) (G : ℕ → C(T, ℝ)) (U V : HeatActionLimit z) (ι : ℕ → ℕ),
      (∀ k a, 0 < F k a) ∧ (∀ k b, 0 < G k b) ∧
      (∀ k a, F k a*(∫ b, hX.canonicalHeatKernel hn p (ε k/4) a b*G k b ∂ν)=1) ∧
      (∀ k b, G k b*(∫ a, hX.canonicalHeatKernel hn p (ε k/4) a b*F k a ∂μ)=1) ∧
      StrictMono ι ∧
      hX.CompactHeatConverges hn p μ F ε hε z ι U.potential ∧
      hX.CompactHeatConverges hn p ν G ε hε z ι V.potential ∧
      (∀ a₀ : S, TendstoUniformly
        (fun k (a : S) => ε (ι k)*(Real.log (F (ι k) a)-Real.log (F (ι k) a₀)))
        (fun a => V.potential (1/2) a₀-V.potential (1/2) a) atTop) ∧
      (∀ b₀ : T, TendstoUniformly
        (fun k (b : T) => ε (ι k)*(Real.log (G (ι k) b)-Real.log (G (ι k) b₀)))
        (fun b => U.potential (1/2) b₀-U.potential (1/2) b) atTop) ∧
      ∀ k s, (hs : 0 < s) → (hst : s < ε k/4) →
        IsProbabilityMeasure ((hausdorff n X).withDensity (fun x => ENNReal.ofReal
          (hX.compactHeatFactor hn p μ (F k) s hs x *
            hX.compactHeatFactor hn p ν (G k) (ε k/4-s) (sub_pos.mpr hst) x))) := by
  classical
  choose F G hF hG hr hc hb using fun k =>
    hX.compact_heat_interpolation hn p hS hT μ ν (ε k/4) (div_pos (hε k) (by norm_num))
  obtain ⟨U,V,ι,hι,hU,hV⟩ := hX.paired_heat_action_limits hn p hK μ ν ρ σ hρ hσ
    hρ0 hσ0 hB hD hμ hν F G hF hG ε hε hε1 hε0 z hR hdS hdT
  have hhalf : ∀ k, ε k*((1:ℝ)/2)/2 = ε k/4 := fun k => by ring
  have hr' (k : ℕ) (a : S) :
      F k a*(∫ b, hX.canonicalHeatKernel hn p (ε k*((1:ℝ)/2)/2) a b*G k b ∂ν)=1 := by
    rw [hhalf]; exact hr k a
  have hc' (k : ℕ) (b : T) :
      G k b*(∫ a, hX.canonicalHeatKernel hn p (ε k*((1:ℝ)/2)/2) b a*F k a ∂μ)=1 := by
    rw [hhalf]
    have he : (fun a : S => hX.canonicalHeatKernel hn p (ε k/4) b a*F k a) =
        (fun a : S => hX.canonicalHeatKernel hn p (ε k/4) a b*F k a) := by
      funext a
      rw [hX.canonicalHeatKernel_symmetric hn p (ε k/4) b a]
    rw [he]
    exact hc k b
  refine ⟨F,G,U,V,ι,hF,hG,hr,hc,hι,hU,hV,?_,?_,?_⟩
  · intro a₀
    exact hX.compact_scaling_boundary_limit hn p ν (fun k => F k) G hF hG ε hε z ι
      V.potential hV (by norm_num) hr' hR hdS a₀
  · intro b₀
    exact hX.compact_scaling_boundary_limit hn p μ (fun k => G k) F hG hF ε hε z ι
      U.potential hU (by norm_num) hc' hR hdT b₀
  · intro k s hs hst
    exact (hb k s hs hst).1

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
