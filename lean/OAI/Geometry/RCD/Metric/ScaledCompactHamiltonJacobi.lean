import OAI.Geometry.RCD.Heat.CompactLogEquation
import OAI.Geometry.RCD.Metric.CompactFactorCenteredCompactness

namespace OAI

/-! # The exact viscous Hamilton--Jacobi equation at small-noise scale

Both the local weak source and the gradient square refer to the same
scaled Sobolev representative of the actual logarithmic heat factor.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_scaled_hamilton_jacobi
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0 < F a) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    {Ω : Set X} (hΩ : IsCompact Ω) :
    ∃ (w : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
      IsWeakLaplacian (hausdorff n X) hX.quadratic w q ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[(hausdorff n X).restrict Ω]
        hX.scaledCompactHeatPotential hn p ν F ε s (div_pos (mul_pos hε hs) (by norm_num))) ∧
      ∀ᵐ x ∂(hausdorff n X).restrict Ω,
        HasDerivAt (fun t => ε * Real.log
          (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν))
          (ε/2*q x + localGamma (hausdorff n X) hX.quadratic w w x/2) s := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  obtain ⟨_u,v,d,_hu,hd,hv,hder,_hmix⟩ := hX.compact_heat_factor_log_equation hn p
    ν ρ hρ hρ0 hB hν F hF (t := ε*s/2) (div_pos (mul_pos hε hs) (by norm_num)) hΩ
  refine ⟨ε • v,ε • d,hd.smul μ Q ε,?_,?_⟩
  · filter_upwards [hv,ae_restrict_of_ae (Lp.coeFn_smul ε (SobolevSpace.toLp μ Q v))]
      with x hx hy
    change SobolevSpace.toLp μ Q (ε • v) x = ε * SobolevSpace.toLp μ Q v x at hy
    rw [hy,hx]
    rfl
  · have hlin : HasDerivAt (fun t : ℝ => ε*t/2) (ε/2) s := by
      have hh := ((hasDerivAt_id s).const_mul ε).div_const 2
      simp only [mul_one,id_eq] at hh
      exact hh
    filter_upwards [hder,ae_restrict_of_ae (Lp.coeFn_smul ε d),
      ae_restrict_of_ae (localGamma_smul_left μ Q ε v (ε • v)),
      ae_restrict_of_ae (localGamma_smul_right μ Q ε v v)] with x hx hq hleft hright
    have hh := ((hx.comp s hlin).const_mul ε)
    convert hh using 1
    · funext t
      rfl
    · change ε/2 * (ε • d) x + localGamma μ Q (ε • v) (ε • v) x/2 = _
      change (ε • d) x = ε*d x at hq
      rw [hq,hleft,hright]
      ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
