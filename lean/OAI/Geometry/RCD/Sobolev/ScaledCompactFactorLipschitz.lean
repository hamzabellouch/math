import OAI.Geometry.RCD.Sobolev.ScaledCompactFactorGradient
import OAI.Geometry.RCD.Sobolev.ContinuousLocalGradientBound

namespace OAI

/-! # Uniform local Lipschitz bounds for small-noise heat potentials

The local weak-gradient estimate applies to the prescribed continuous
logarithm, so no noise-dependent choice of representative is made.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_scaled_lipschitz :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x|≤B) →
        ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0<F a) →
        ∀ {ε s δ : ℝ} (hε : 0<ε) (_hε1 : ε≤1) (hδ : 0<δ) (hδs : δ≤ s) (_hs1 : s≤1),
        ∀ (z : X) (R : ℝ), 0≤R → (∀ a : S, dist z a≤R) → ∀ {r : ℝ}, 0<r →
          LipschitzOnWith
            ⟨Real.sqrt (Real.exp |K| * (4*C/δ+16*D*(R+8*r)^2/δ^2)),Real.sqrt_nonneg _⟩
            (fun x => ε*Real.log (hX.compactHeatFactor hn p ν F (ε*s/2)
              (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num)) x)) (ball z r) := by
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_scaled_gradient hn p
  refine ⟨C,D,hC,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε s δ hε hε1 hδ hδs hs1 z R hR hdist r hr
  let μ := hausdorff n X
  let Q := hX.quadratic
  let H := hX.compactHeatFactor hn p ν F (ε*s/2)
    (div_pos (mul_pos hε (hδ.trans_le hδs)) (by norm_num))
  let M := Real.exp |K| * (4*C/δ+16*D*(R+8*r)^2/δ^2)
  let L : ℝ≥0 := ⟨Real.sqrt M,Real.sqrt_nonneg _⟩
  have hM : 0≤M := by dsimp only [M]; positivity
  have hL : (L:ℝ)^2=M := by
    change (Real.sqrt M)^2=M
    exact Real.sq_sqrt hM
  obtain ⟨v,_q,_hq,hv,hgrad⟩ := hdata ν ρ hρ hρ0 hB hν F hF hε hε1 hδ hδs hs1
    z R hR hdist (closedBall z (8*r)) (isCompact_closedBall z (8*r))
  have hlog : Continuous (fun x => ε*Real.log (H x)) := by
    apply continuous_const.mul
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (Real.continuousAt_log (hX.compactHeatFactor_positive hn p ν F hF _ _ x).ne').comp
      H.continuous.continuousAt
  have hrep : SobolevSpace.toLp μ Q v =ᵐ[μ.restrict (ball z (8*r))] fun x => ε*Real.log (H x) :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hv
  have hg : ∀ᵐ x ∂μ.restrict (ball z (8*r)), localGamma μ Q v v x≤(L:ℝ)^2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hgrad,
      ae_restrict_of_ae (localGamma_self μ Q v),ae_restrict_mem measurableSet_ball] with x hx he hm
    rw [he]
    have hd : dist z x≤8*r := (mem_ball'.mp hm).le
    have hsq : (R+dist z x)^2≤(R+8*r)^2 :=
      pow_le_pow_left₀ (add_nonneg hR dist_nonneg) (add_le_add le_rfl hd) 2
    have hbound : Real.exp |K| * (4*C/δ+16*D*(R+dist z x)^2/δ^2)≤M := by
      dsimp only [M]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by positivity)) (sq_nonneg δ)
    rw [hL]
    exact hx.trans hbound
  exact hX.continuous_local_gradient_lipschitz hn v _ z hr L hlog.continuousOn hrep hg

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
