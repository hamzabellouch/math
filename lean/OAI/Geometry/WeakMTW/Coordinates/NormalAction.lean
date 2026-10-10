import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalNeighborhood
import OAI.Geometry.WeakMTW.Geodesics.FlowFirstVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

 def action (N : NormalFlow G S x₀) (q : E × E) : ℝ := N.time^2/2 * G q.1 q.2 q.2

 omit [FiniteDimensional ℝ E] in
 theorem normal_smooth (N : NormalFlow G S x₀) : ContDiffOn ℝ ∞ N.normal N.normal.source := by
   have hh : ContDiffOn ℝ ∞ (fun q => (q.1, (N.flow (N.time,q)).1)) N.normal.source :=
     contDiffOn_fst.prodMk ((N.flow_smooth.comp
       (contDiff_const.prodMk contDiff_id).contDiffOn
       (fun q hq => N.source_stays q hq _ ⟨N.time_pos.le,le_rfl⟩)).fst)
   exact hh.congr (fun q _ => N.normal_apply q)

 omit [FiniteDimensional ℝ E] in
 theorem action_hasFDerivAt (N : NormalFlow G S x₀) {q : E × E}
    (hq : DifferentiableAt ℝ G q.1) :
    HasFDerivAt N.action
      ((N.time^2/2 : ℝ) •
        (((G q.1 q.2).comp (.snd ℝ E E)) +
          ((G q.1).comp (.snd ℝ E E) + (fderiv ℝ G q.1 ∘L .fst ℝ E E).flip q.2).flip q.2)) q := by
   have hp : HasFDerivAt (Prod.fst : E × E → E) (.fst ℝ E E) q := hasFDerivAt_fst
   have hB := HasFDerivAt.comp (𝕜 := ℝ) (f := Prod.fst) (g := G) q hq.hasFDerivAt hp
   have hν : HasFDerivAt (fun z : E × E => z.2) (.snd ℝ E E) q := hasFDerivAt_snd
   have hh := (hB.clm_apply hν).clm_apply hν
   exact hh.const_mul (N.time^2/2)

 theorem action_derivative (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ y ∈ S, ∀ v w, G y v w = G y w v)
    (hpos : ∀ y ∈ S, ∀ v : E, v ≠ 0 → 0 < G y v v)
    {q : E × E} (hq : q ∈ N.normal.source) (w : E × E) :
    fderiv ℝ N.action q w = N.time *
      (G (N.flow (N.time,q)).1 (N.flow (N.time,q)).2 (fderiv ℝ N.normal q w).2 -
        G q.1 q.2 w.1) := by
   have hqS : q.1 ∈ S := by
     have hh := (N.ode _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)).1
     simpa only [N.initial _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)] using hh
   have hDG := ((hG _ hqS).contDiffAt (hS.mem_nhds hqS)).differentiableAt (by simp)
   have hΦ := ((N.flow_smooth _ (N.source_stays q hq _ ⟨N.time_pos.le,le_rfl⟩)).contDiffAt
     (N.domain_open.mem_nhds (N.source_stays q hq _ ⟨N.time_pos.le,le_rfl⟩))).differentiableAt (by simp)
   have hF := hΦ.hasFDerivAt.comp q ((hasFDerivAt_const N.time q).prodMk (hasFDerivAt_id q))
   have hN : HasFDerivAt N.normal ((ContinuousLinearMap.fst ℝ E E).prod
       ((ContinuousLinearMap.fst ℝ E E).comp (fderiv ℝ N.flow (N.time,q) ∘L
         ((0 : E × E →L[ℝ] ℝ).prod (.id ℝ (E × E)))))) q := by
     have hh := hasFDerivAt_fst.prodMk hF.fst
     exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => N.normal_apply z))
   have hv := FirstVariation.flow_first_variation hS hG hsym hpos N.domain_open
     N.flow_smooth N.initial N.ode N.time_pos.le (N.source_stays q hq) w
   rw [(N.action_hasFDerivAt hDG).fderiv, hN.fderiv]
   simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
     zero_apply,ContinuousLinearMap.id_apply,
     add_apply,ContinuousLinearMap.flip_apply,
     smul_apply,smul_eq_mul]
   change N.time^2/2 * (G q.1 q.2 w.2 + (G q.1 w.2 q.2 + fderiv ℝ G q.1 w.1 q.2 q.2)) =
     N.time * (G (N.flow (N.time,q)).1 (N.flow (N.time,q)).2
       (fderiv ℝ N.flow (N.time,q) (0,w)).1 - G q.1 q.2 w.1)
   rw [hsym q.1 hqS w.2 q.2]
   rw [hv]
   ring

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
