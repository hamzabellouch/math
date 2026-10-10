import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.ShortChartAction
import OAI.Geometry.WeakMTW.Coordinates.ChartGlobalVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def crossFlowCoordinates (x y : M) (t : ℝ) (q : Model n × Model n) : Model n × Model n :=
    stateChart y (geodesicFlow t ((stateChart x).symm q))

 theorem crossFlowCoordinates_step (x y : M) {s : ℝ} {q : Model n × Model n}
    (hs : geodesicFlow s ((stateChart x).symm q) ∈ (stateChart y).source) (t : ℝ) :
    flowCoordinates y t (crossFlowCoordinates x y s q) = crossFlowCoordinates x y (t+s) q := by
  dsimp only [flowCoordinates,crossFlowCoordinates]
  rw [(stateChart y).left_inv hs,← geodesicFlow_add]

 def generatingAction (x y : M) (ε : ℝ) (Q : (Model n × Model n) × Model n) : ℝ :=
    (1-ε)*chartKinetic x Q.1 + ε⁻¹ * chartCost y ((crossFlowCoordinates x y (1-ε) Q.1).1,Q.2)

 theorem generatingAction_smooth (x y : M) {ε : ℝ} {q : Model n × Model n}
    (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (hshort : ShortChartAction y ε (crossFlowCoordinates x y (1-ε) q)) :
    ContDiffAt ℝ ∞ (generatingAction x y ε)
      (q,(crossFlowCoordinates x y 1 q).1) := by
  have hstep : flowCoordinates y ε (crossFlowCoordinates x y (1-ε) q) = crossFlowCoordinates x y 1 q := by
     rw [crossFlowCoordinates_step x y hτ ε]
     congr 1
     ring
  have hK := (chartKinetic_smooth x q hq).contDiffAt ((stateChart x).open_target.mem_nhds hq)
  have hΦ := chart_flow_smooth x y (1-ε) hq hτ
  have hC := hshort.2.2.1
  rw [hstep] at hC
  have harg : ContDiffAt ℝ ∞ (fun Q : (Model n × Model n) × Model n =>
      ((crossFlowCoordinates x y (1-ε) Q.1).1,Q.2)) (q,(crossFlowCoordinates x y 1 q).1) :=
    (ContDiffAt.comp (f := Prod.fst) (g := fun r => (crossFlowCoordinates x y (1-ε) r).1)
      _ hΦ.fst contDiffAt_fst).prodMk contDiffAt_snd
  exact (contDiffAt_const.mul (ContDiffAt.comp (f := Prod.fst) (g := chartKinetic x)
    (q,(crossFlowCoordinates x y 1 q).1) hK contDiffAt_fst)).add
    (contDiffAt_const.mul (ContDiffAt.comp (f := fun Q : (Model n × Model n) × Model n =>
      ((crossFlowCoordinates x y (1-ε) Q.1).1,Q.2)) (g := chartCost y)
      (q,(crossFlowCoordinates x y 1 q).1) hC harg))

 theorem generatingAction_gradient (x y : M) {ε : ℝ} (hε : ε ≠ 0)
    {q : Model n × Model n} (hq : q ∈ (stateChart x).target)
    (hτ : geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source)
    (hshort : ShortChartAction y ε (crossFlowCoordinates x y (1-ε) q))
    (k : Model n × Model n) (z : Model n) :
    fderiv ℝ (generatingAction x y ε) (q,(crossFlowCoordinates x y 1 q).1) (k,z) =
      metric y (crossFlowCoordinates x y 1 q).1 (crossFlowCoordinates x y 1 q).2 z -
      metric x q.1 q.2 k.1 := by
  let τ := 1-ε
  let Φ := crossFlowCoordinates (n := n) x y τ
  let Ψ := crossFlowCoordinates (n := n) x y 1
  let Q := (q,(Ψ q).1)
  have hstep : flowCoordinates y ε (Φ q) = Ψ q := by
    change flowCoordinates y ε (crossFlowCoordinates x y (1-ε) q) = crossFlowCoordinates x y 1 q
    rw [crossFlowCoordinates_step x y hτ ε]
    congr 1
    ring
  have hK := ((chartKinetic_smooth x q hq).contDiffAt ((stateChart x).open_target.mem_nhds hq)).differentiableAt (by simp)
  have hΦ : DifferentiableAt ℝ Φ q := (chart_flow_smooth x y τ hq hτ).differentiableAt (by simp)
  have hC := hshort.2.2.1.differentiableAt (by simp)
  rw [hstep] at hC
  have h₁ := hK.hasFDerivAt.comp Q (hasFDerivAt_fst (𝕜 := ℝ))
  have h₂ := (hΦ.hasFDerivAt.comp Q (hasFDerivAt_fst (𝕜 := ℝ))).fst.prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := Q))
  have h₃ := hC.hasFDerivAt.comp Q h₂
  have hd := (h₁.const_mul τ).add (h₃.const_mul ε⁻¹)
  have hDf : fderiv ℝ (generatingAction x y ε) Q =
      τ • ((fderiv ℝ (chartKinetic x) q).comp (ContinuousLinearMap.fst ℝ (Model n × Model n) (Model n))) +
      ε⁻¹ • ((fderiv ℝ (chartCost y) ((Φ q).1,(Ψ q).1)).comp
        (((ContinuousLinearMap.fst ℝ (Model n) (Model n)).comp
          ((fderiv ℝ Φ q).comp (ContinuousLinearMap.fst ℝ (Model n × Model n) (Model n)))).prod
          (ContinuousLinearMap.snd ℝ (Model n × Model n) (Model n)))) := hd.fderiv
  rw [hDf]
  change τ * fderiv ℝ (chartKinetic x) q k + ε⁻¹ *
    fderiv ℝ (chartCost y) ((Φ q).1,(Ψ q).1) ((fderiv ℝ Φ q k).1,z) =
    metric y (Ψ q).1 (Ψ q).2 z - metric x q.1 q.2 k.1
  have hshortD := hshort.2.2.2 ((fderiv ℝ Φ q k).1,z)
  rw [hstep] at hshortD
  change fderiv ℝ (chartCost y) ((Φ q).1,(Ψ q).1) ((fderiv ℝ Φ q k).1,z) =
    ε * (metric y (Ψ q).1 (Ψ q).2 z - metric y (Φ q).1 (Φ q).2 (fderiv ℝ Φ q k).1) at hshortD
  rw [hshortD]
  have hb := chart_flow_boundary x y τ hq hτ k
  change metric y (Φ q).1 (Φ q).2 (fderiv ℝ Φ q k).1 = metric x q.1 q.2 k.1 + τ * fderiv ℝ (chartKinetic x) q k at hb
  rw [hb]
  field_simp [hε]
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
