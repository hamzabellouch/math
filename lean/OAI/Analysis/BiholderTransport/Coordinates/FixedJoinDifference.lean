import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FixedJoinMiddle
import OAI.Analysis.BiholderTransport.CostGeometry.DividedPullback

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedJoinMiddle_difference_normal {x z : M} {h T t : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {q : TangentSpace 𝓘(ℝ,Model n) z}
    {g : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) z}
    (ht : t≠0) (htime : T-h=(1-h)*t)
    (hq : q∈injectivityDomain z) (htq : t • q∈injectivityDomain z)
    (hq1 : riemannianExp z q=riemannianExp x p)
    (hqT : riemannianExp z (t • q)=riemannianExp x (T • p))
    (hg : ContDiffAt ℝ 2 g p) (hg0 : g p=0)
    (hgi : ∀ᶠ b in 𝓝 p, riemannianExp z (g b)=riemannianExp x (h • b))
    (hBT : ContDiffAt ℝ 2 (fixedJoinAction x h T p) (0,p))
    (hB1 : ContDiffAt ℝ 2 (fixedJoinAction x h 1 p) (0,p))
    (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p k k-fixedJoinMiddle x h 1 p k k=
      (hessianValue z (t • q) (fderiv ℝ g p k)/t-
        hessianValue z q (fderiv ℝ g p k))/(1-h) := by
  have hST := hBT.comp p (contDiffAt_const.prodMk contDiffAt_id)
  have hS1 := hB1.comp p (contDiffAt_const.prodMk contDiffAt_id)
  change ContDiffAt ℝ 2 (fun b => fixedJoinAction x h T p (0,b)) p at hST
  change ContDiffAt ℝ 2 (fun b => fixedJoinAction x h 1 p (0,b)) p at hS1
  have he : (fun b => fixedJoinAction x h T p (0,b)-fixedJoinAction x h 1 p (0,b)) =ᶠ[𝓝 p]
      (fun b => (1-h)⁻¹*(normalCost z (t • q) (g b)/t-normalCost z q (g b))) := by
    filter_upwards [hgi] with b hb
    simp only [fixedJoinAction,normalCost,hb,hq1,hqT,one_smul,htime,div_eq_mul_inv,mul_inv_rev]
    ring
  have H := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A k k) (he.fderiv (𝕜 := ℝ)).fderiv_eq
  rw [second_fderiv_sub hST hS1,second_fderiv_const_mul,
    divided_cost_difference_pullback hq htq ht hg hg0] at H
  rw [fixedJoinMiddle_eq_slice hBT,fixedJoinMiddle_eq_slice hB1]
  simpa only [div_eq_mul_inv,mul_comm] using H

end WeakMTWTransport

end

end OAI
