import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ProximalSelectorDerivative
import OAI.Analysis.BiholderTransport.Calculus.SecondTaylorComposition
import OAI.Analysis.BiholderTransport.Convexity.ProximalProducer

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma semiconvex_phase_graph_derivative
    {f:E → ℝ} {Y:E → E} {P:E → E →L[ℝ] ℝ}
    {Φ:(E×(E →L[ℝ] ℝ)) → E×(E →L[ℝ] ℝ)}
    {x p:E} {A R:E →L[ℝ] E} {H:E →L[ℝ] E →L[ℝ] ℝ}
    {D:(E×(E →L[ℝ] ℝ)) →L[ℝ] E×(E →L[ℝ] ℝ)}
    (hA:∀v w,inner ℝ (A v) w=inner ℝ v (A w))
    (hexp:HasQuadraticExpansion (fun h=>f (Y x+h)) p A)
    {r:ℝ} (hr:0<r) (K:ℝ)
    (hY:HasFDerivAt Y R x) (hP:HasFDerivAt P H x)
    (hΦ:HasFDerivAt Φ D (x,P x))
    (hbase:∀ᶠ z in 𝓝 x,(Φ (z,P z)).1=Y z)
    (hsub:∀ᶠ z in 𝓝 x,
      IsSemiconvexSubgradientOn f (Metric.ball (Y x) r) K (Y z)
        ((InnerProductSpace.toDual ℝ E).symm (Φ (z,P z)).2)) :
    D.comp ((ContinuousLinearMap.id ℝ E).prod H)=
      R.prod (((innerSL ℝ).comp A).comp R) := by
  let ξ:=fun z=>(InnerProductSpace.toDual ℝ E).symm (Φ (z,P z)).2
  have hξ:ξ x=p:=semiconvex_subgradient_eq_at_expansion hA hexp hr K hsub.self_of_nhds
  have hd:=semiconvex_subgradient_along_selector hA hexp hr K hY hξ hsub
  have hs:HasFDerivAt (fun z=>(Φ (z,P z)).2) (((innerSL ℝ).comp A).comp R) x := by
    have hh:HasFDerivAt (fun z=>(innerSL ℝ) (ξ z)) ((innerSL ℝ).comp (A.comp R)) x :=
      (innerSL ℝ).hasFDerivAt.comp x hd
    have he:(fun z=>(Φ (z,P z)).2)=(fun z=>(innerSL ℝ) (ξ z)) := by
      funext z
      exact ((InnerProductSpace.toDual ℝ E).apply_symm_apply (Φ (z,P z)).2).symm
    rw [he]
    simpa only [ContinuousLinearMap.comp_assoc] using hh
  have hb:HasFDerivAt (fun z=>(Φ (z,P z)).1) R x := hY.congr_of_eventuallyEq hbase
  have hboth:=hb.prodMk hs
  have hchain:=hΦ.comp x ((hasFDerivAt_id x).prodMk hP)
  exact hchain.unique hboth

end WeakMTWTransport

end

end OAI
