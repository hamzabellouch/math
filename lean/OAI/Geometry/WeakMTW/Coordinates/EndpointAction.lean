import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalNeighborhood
import OAI.Geometry.WeakMTW.Coordinates.NormalAction

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

 def endpointAction (N : NormalFlow G S x₀) (q : E × E) : ℝ := N.action (N.normal.symm q)

omit [FiniteDimensional ℝ E] in
 theorem inverse_fst (N : NormalFlow G S x₀) {q : E × E} (hq : q ∈ N.normal.target) :
    (N.normal.symm q).1 = q.1 := by
   have hh := congrArg Prod.fst (N.normal.right_inv hq)
   simpa only [N.normal_apply] using hh

omit [FiniteDimensional ℝ E] in
 theorem action_smooth (N : NormalFlow G S x₀) (_ : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) : ContDiffOn ℝ ∞ N.action N.normal.source := by
   have hmem : ∀ q ∈ N.normal.source, q.1 ∈ S := by
     intro q hq
     have hh := (N.ode _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)).1
     simpa only [N.initial _ (N.source_stays q hq 0 ⟨le_rfl,N.time_pos.le⟩)] using hh
   exact contDiffOn_const.mul (((hG.comp contDiffOn_fst hmem).clm_apply contDiffOn_snd).clm_apply contDiffOn_snd)

omit [FiniteDimensional ℝ E] in
 theorem endpointAction_smooth (N : NormalFlow G S x₀) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) : ContDiffOn ℝ ∞ N.endpointAction N.normal.target :=
   (N.action_smooth hS hG).comp N.inverse_smooth (fun _ h => N.normal.map_target h)

 theorem endpointAction_derivative (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ y ∈ S, ∀ v w, G y v w = G y w v)
    (hpos : ∀ y ∈ S, ∀ v : E, v ≠ 0 → 0 < G y v v)
    {q : E × E} (hq : q ∈ N.normal.target) (w : E × E) :
    fderiv ℝ N.endpointAction q w = N.time *
      (G (N.flow (N.time,N.normal.symm q)).1 (N.flow (N.time,N.normal.symm q)).2 w.2 -
        G q.1 (N.normal.symm q).2 w.1) := by
   let p := N.normal.symm q
   have hp : p ∈ N.normal.source := N.normal.map_target hq
   have hi : DifferentiableAt ℝ N.normal.symm q :=
     ((N.inverse_smooth _ hq).contDiffAt (N.normal.open_target.mem_nhds hq)).differentiableAt (by simp)
   have hn : DifferentiableAt ℝ N.normal p :=
     ((N.normal_smooth _ hp).contDiffAt (N.normal.open_source.mem_nhds hp)).differentiableAt (by simp)
   have ha : DifferentiableAt ℝ N.action p :=
     ((N.action_smooth hS hG _ hp).contDiffAt (N.normal.open_source.mem_nhds hp)).differentiableAt (by simp)
   have hid : (N.normal ∘ N.normal.symm) =ᶠ[𝓝 q] id := by
     filter_upwards [N.normal.open_target.mem_nhds hq] with z hz
     exact N.normal.right_inv hz
   have hcomp : HasFDerivAt (N.normal ∘ N.normal.symm)
       (fderiv ℝ N.normal p ∘L fderiv ℝ N.normal.symm q) q :=
     HasFDerivAt.comp (f := N.normal.symm) (g := N.normal) q hn.hasFDerivAt hi.hasFDerivAt
   have hdi := hcomp.unique ((hasFDerivAt_id q).congr_of_eventuallyEq hid)
   have hw := congrArg (fun L : E × E →L[ℝ] E × E => L w) hdi
   have hfst : (fun z : E × E => (N.normal.symm z).1) =ᶠ[𝓝 q] Prod.fst := by
     filter_upwards [N.normal.open_target.mem_nhds hq] with z hz
     exact N.inverse_fst hz
   have hdf := hfst.fderiv_eq (𝕜 := ℝ)
   rw [hi.hasFDerivAt.fst.fderiv,hasFDerivAt_fst.fderiv] at hdf
   have hwf := congrArg (fun L : E × E →L[ℝ] E => L w) hdf
   have hAction : HasFDerivAt N.endpointAction
       (fderiv ℝ N.action p ∘L fderiv ℝ N.normal.symm q) q :=
     HasFDerivAt.comp (f := N.normal.symm) (g := N.action) q ha.hasFDerivAt hi.hasFDerivAt
   rw [hAction.fderiv,ContinuousLinearMap.comp_apply,N.action_derivative hS hG hsym hpos hp]
   simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hw
   change (fderiv ℝ N.normal.symm q w).1 = w.1 at hwf
   rw [hw,hwf,N.inverse_fst hq]

end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
