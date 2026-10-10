import OAI.Geometry.RCD.Heat.CompactHeatVelocityDecomposition
import OAI.Geometry.RCD.Heat.HessianForwardOsmotic

namespace OAI

/-! # Exact forward-action decomposition of the actual velocity Hessian -/

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

theorem velocity_constant_difference (k : ℕ) (t : Ioo (0:ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ (t:ℝ)/2) (z : X) (Ω : Set X)
    (θ η u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic θ
      =ᵐ[(hausdorff n X).restrict Ω] D.velocityPotential k t)
    (hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η
      =ᵐ[(hausdorff n X).restrict Ω] D.osmoticPotential k t)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict Ω]
        hX.fixedGaugeScaledPotential hn p μ (D.left k) (ε k) (hε k) δ hδ z (t/2)) :
    SobolevSpace.toLp (hausdorff n X) hX.quadratic (θ-(η-(1/2:ℝ) • u))
      =ᵐ[(hausdorff n X).restrict Ω] fun _ =>
        -(ε k/2)*Real.log (hX.compactHeatFactor hn p μ (D.left k) (ε k) (hε k) z) := by
  let m := hausdorff n X
  let q := hX.quadratic
  filter_upwards [hθ,hη,hu,
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp m q θ)
      (SobolevSpace.toLp m q (η-(1/2:ℝ) • u))),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp m q η)
      (SobolevSpace.toLp m q ((1/2:ℝ) • u))),
    ae_restrict_of_ae (Lp.coeFn_smul (1/2:ℝ) (SobolevSpace.toLp m q u))]
    with x hx hy hz hsub hsub' hsmul
  change SobolevSpace.toLp m q (θ-(η-(1/2:ℝ) • u)) x =
    SobolevSpace.toLp m q θ x-SobolevSpace.toLp m q (η-(1/2:ℝ) • u) x at hsub
  change SobolevSpace.toLp m q (η-(1/2:ℝ) • u) x =
    SobolevSpace.toLp m q η x-SobolevSpace.toLp m q ((1/2:ℝ) • u) x at hsub'
  change SobolevSpace.toLp m q ((1/2:ℝ) • u) x = (1/2:ℝ)*SobolevSpace.toLp m q u x at hsmul
  rw [hsub,hsub',hsmul,hx,hy,hz]
  exact D.velocity_fixed_gauge_identity k t hδ ht z x

theorem velocity_hessian_decomposition (k : ℕ) (t : Ioo (0:ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ (t:ℝ)/2) (z : X) (Ω : Set X)
    (w θ η u Wθ Wη Wu Gθ Gη Gu Gηu : SobolevSpace (hausdorff n X) hX.quadratic)
    (hθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic θ
      =ᵐ[(hausdorff n X).restrict Ω] D.velocityPotential k t)
    (hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η
      =ᵐ[(hausdorff n X).restrict Ω] D.osmoticPotential k t)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict Ω]
        hX.fixedGaugeScaledPotential hn p μ (D.left k) (ε k) (hε k) δ hδ z (t/2))
    (hWθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wθ
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic w θ)
    (hWη : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wη
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic w η)
    (hWu : SobolevSpace.toLp (hausdorff n X) hX.quadratic Wu
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic w u)
    (hGθ : SobolevSpace.toLp (hausdorff n X) hX.quadratic Gθ
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic θ θ)
    (hGη : SobolevSpace.toLp (hausdorff n X) hX.quadratic Gη
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic η η)
    (hGu : SobolevSpace.toLp (hausdorff n X) hX.quadratic Gu
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic u u)
    (hGηu : SobolevSpace.toLp (hausdorff n X) hX.quadratic Gηu
      =ᵐ[(hausdorff n X).restrict Ω] localGamma (hausdorff n X) hX.quadratic η u) :
    (fun x => localHessianAction (hausdorff n X) hX.quadratic w θ θ Wθ Wθ Gθ x-
      localHessianAction (hausdorff n X) hX.quadratic w η η Wη Wη Gη x)
      =ᵐ[(hausdorff n X).restrict Ω] fun x =>
        (1/4:ℝ)*localHessianAction (hausdorff n X) hX.quadratic w u u Wu Wu Gu x-
          localHessianAction (hausdorff n X) hX.quadratic w η u Wη Wu Gηu x := by
  let m := hausdorff n X
  let q := hX.quadratic
  obtain ⟨hW,hG⟩ := localGamma_forward_osmotic_reps m q w η u Wη Wu Gη Gu Gηu
    hWη hWu hGη hGu hGηu
  have hd := D.velocity_constant_difference k t hδ ht z Ω θ η u hθ hη hu
  have he := localHessianAction_constant_directions m q w θ (η-(1/2:ℝ) • u)
    θ (η-(1/2:ℝ) • u) Wθ (Wη-(1/2:ℝ) • Wu) Wθ (Wη-(1/2:ℝ) • Wu)
    Gθ (Gη-Gηu+(1/4:ℝ) • Gu) _ _ hd hd hWθ hW hWθ hW hGθ hG
  filter_upwards [he,ae_restrict_of_ae
    (localHessianAction_forward_osmotic m q w η u Wη Wu Gη Gu Gηu)] with x hx hy
  rw [hx,hy]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
