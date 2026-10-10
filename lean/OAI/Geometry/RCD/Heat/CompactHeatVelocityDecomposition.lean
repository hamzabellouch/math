import OAI.Geometry.RCD.Heat.CompactHeatVelocityPotential
import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential
import OAI.Geometry.RCD.Metric.InwardLocality

namespace OAI

/-! # The physical velocity is osmotic velocity minus half the forward action gradient -/

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

theorem velocity_fixed_gauge_identity (k : ℕ) (t : Ioo (0:ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ (t:ℝ)/2) (z x : X) :
    D.velocityPotential k t x - (D.osmoticPotential k t x -
      (1/2:ℝ)*hX.fixedGaugeScaledPotential hn p μ (D.left k) (ε k) (hε k) δ hδ z (t/2) x) =
      -(ε k/2)*Real.log (hX.compactHeatFactor hn p μ (D.left k) (ε k) (hε k) z) := by
  rw [hX.fixedGaugeScaledPotential_eq hn p μ (D.left k) (ε k) (hε k) δ hδ z ht x]
  dsimp only [velocityPotential,osmoticPotential,interpolationDensity,scaledCompactHeatPotential]
  rw [Real.log_mul
    (hX.compactHeatFactor_positive hn p μ (D.left k) (D.left_pos k) _ _ x).ne'
    (hX.compactHeatFactor_positive hn p ν (D.right k) (D.right_pos k) _ _ x).ne']
  have htime : ε k*((t:ℝ)/2)/2 = ε k/4*t := by ring
  have he : hX.compactHeatFactor hn p μ (D.left k) (ε k*((t:ℝ)/2)/2)
      (div_pos (mul_pos (hε k) (hδ.trans_le ht)) (by norm_num)) x =
      hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t)
        (mul_pos (div_pos (hε k) (by norm_num)) t.property.1) x := by
    simp only [htime]
  rw [he]
  ring

theorem velocity_gamma_decomposition (k : ℕ) (t : Ioo (0:ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ (t:ℝ)/2) (z : X) (Ω : Set X)
    (θ η u w : SobolevSpace (hausdorff n X) hX.quadratic)
    (hθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic θ
      =ᵐ[(hausdorff n X).restrict Ω] D.velocityPotential k t)
    (hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η
      =ᵐ[(hausdorff n X).restrict Ω] D.osmoticPotential k t)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict Ω]
        hX.fixedGaugeScaledPotential hn p μ (D.left k) (ε k) (hε k) δ hδ z (t/2)) :
    localGamma (hausdorff n X) hX.quadratic θ w =ᵐ[(hausdorff n X).restrict Ω]
      fun x => localGamma (hausdorff n X) hX.quadratic η w x -
        (1/2:ℝ)*localGamma (hausdorff n X) hX.quadratic u w x := by
  let m := hausdorff n X
  let q := hX.quadratic
  have hd : SobolevSpace.toLp m q (θ-(η-(1/2:ℝ) • u)) =ᵐ[m.restrict Ω]
      fun _ => -(ε k/2)*Real.log (hX.compactHeatFactor hn p μ (D.left k) (ε k) (hε k) z) := by
    filter_upwards [hθ,hη,hu,
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp m q θ)
        (SobolevSpace.toLp m q (η-(1/2:ℝ) • u))),
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp m q η)
        (SobolevSpace.toLp m q ((1/2:ℝ) • u))),
      ae_restrict_of_ae (Lp.coeFn_smul (1/2:ℝ) (SobolevSpace.toLp m q u))]
      with x hx hy hu hsub hsub' hsmul
    change SobolevSpace.toLp m q (θ-(η-(1/2:ℝ) • u)) x =
      SobolevSpace.toLp m q θ x-SobolevSpace.toLp m q (η-(1/2:ℝ) • u) x at hsub
    change SobolevSpace.toLp m q (η-(1/2:ℝ) • u) x =
      SobolevSpace.toLp m q η x-SobolevSpace.toLp m q ((1/2:ℝ) • u) x at hsub'
    change SobolevSpace.toLp m q ((1/2:ℝ) • u) x = (1/2:ℝ)*SobolevSpace.toLp m q u x at hsmul
    rw [hsub,hsub',hsmul,hx,hy,hu]
    exact D.velocity_fixed_gauge_identity k t hδ ht z x
  have he := localGamma_eq_of_constant_difference m q Ω θ (η-(1/2:ℝ) • u) w _ hd
  filter_upwards [he,ae_restrict_of_ae (localGamma_sub_left m q η ((1/2:ℝ) • u) w),
    ae_restrict_of_ae (localGamma_smul_left m q (1/2:ℝ) u w)] with x hx hy hz
  rw [hx,hy,hz]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
