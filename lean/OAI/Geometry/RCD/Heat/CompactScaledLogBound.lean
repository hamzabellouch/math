import OAI.Geometry.RCD.Sobolev.ScaledCompactFactorGradient

namespace OAI

/-! # A uniform local bound for all scaled compact-factor logarithms -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_scaled_log_uniform_bound {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (z : X) {R r δ : ℝ} (hR : 0 ≤ R) (hdist : ∀ a : S, dist z a ≤ R)
    (hδ : 0 < δ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (F : C(S,ℝ)), (∀ a, 0 < F a) →
      ∀ {c s : ℝ} (hc : 0 < c) (_hc2 : 2*c ≤ 1) (hδs : δ ≤ s) (_hs1 : s ≤ 1),
      ∃ P : SobolevSpace (hausdorff n X) hX.quadratic,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic P
          =ᵐ[(hausdorff n X).restrict (closedBall z r)] fun x =>
            (2*c)*Real.log (hX.compactHeatFactor hn p ν F (c*s)
              (mul_pos hc (hδ.trans_le hδs)) x)) ∧
        ∀ᵐ x ∂(hausdorff n X).restrict (closedBall z r),
          (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic P x)^2 ≤ H := by
  obtain ⟨C,D,hC,hD,hdata⟩ := hX.compact_heat_factor_scaled_gradient hn p
  let H := Real.exp |K| *(4*C/δ+16*D*(R+r)^2/δ^2)
  refine ⟨H,by dsimp only [H]; positivity,?_⟩
  intro F hF c s hc hc2 hδs hs1
  obtain ⟨P,q,hq,hP,hg⟩ := hdata ν ρ hρ hρ0 hB hν F hF
    (show 0 < 2*c by positivity) hc2 hδ hδs hs1 z R hR hdist
    (closedBall z r) (isCompact_closedBall z r)
  refine ⟨P,?_,?_⟩
  · have he : 2*c*s/2=c*s := by ring
    simpa only [he] using hP
  · filter_upwards [hg,ae_restrict_mem measurableSet_closedBall] with x hx hmem
    have hxr : dist z x ≤ r := by simpa only [dist_comm] using mem_closedBall.mp hmem
    have hp : (R+dist z x)^2 ≤ (R+r)^2 :=
      pow_le_pow_left₀ (add_nonneg hR dist_nonneg) (by linarith) 2
    apply hx.trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity)) (sq_nonneg δ))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
