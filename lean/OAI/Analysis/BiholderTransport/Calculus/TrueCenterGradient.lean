import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveDifferentiability
import OAI.Analysis.BiholderTransport.Coordinates.Taylor
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.Contact.LocalCEMS
import OAI.Analysis.BiholderTransport.Contact.CenterSupportFamily

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

lemma reverse_minimizer_eq {a c:M}
    {r:TangentSpace 𝓘(ℝ,Model n) c} {q:TangentSpace 𝓘(ℝ,Model n) a}
    (hr:r∈injectivityDomain c) (hq:q∈minimizingVectors a)
    (ha:riemannianExp c r=a) (hc:riemannianExp a q=c) :
    reverseRay (⟨c,r⟩:TangentBundle 𝓘(ℝ,Model n) M)=⟨a,q⟩ := by
  let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨c,r⟩
  have hb:(reverseRay z).1=a:=(reverseRay_base z).trans ha
  have hR:=reverseRay_regular (z:=z) hr
  have hE:=reverseRay_endpoint z
  generalize hw:reverseRay z=w
  rw [hw] at hb hR hE
  rcases w with ⟨b,p⟩
  change b=a at hb
  subst b
  have he:=riemannianExp_interior_unique hR hq (hE.trans hc.symm)
  exact congrArg (fun v:TangentSpace 𝓘(ℝ,Model n) a=>(⟨a,v⟩:TangentBundle 𝓘(ℝ,Model n) M)) he

lemma NormalAlexandrovContact.active_eq {u:M → ℝ} (hu:Continuous u) {y:M}
    {p r:TangentSpace 𝓘(ℝ,Model n) y}
    {A:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y}
    (hA:NormalAlexandrovContact (n:=n) u y p A) (hr:r∈activeLogs u y) : r=p := by
  have H:=activeLog_derivative_eq hu hr hA.2.2.2.hasFDerivAt
  apply ext_inner_right ℝ
  intro d
  exact (congrArg (fun L:TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ=>L d) H).symm

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma TrueCenterRow.active {c:M} {u v:M → ℝ} (hdual:IsCostDualPair u v)
    {φ:ℝ → ℝ} {x:Model n} {z:M} {τ l:ℝ} (R:TrueCenterRow c u v φ x z τ l) :
    chartFiberInverse c x R.r∈activeLogs u ((extChartAt 𝓘(ℝ,Model n) c).symm x) := by
  refine ⟨R.minimizing,?_⟩
  have H:=R.contact
  rw [movingNormal_eq R.chart] at H
  simpa only [contactGap,hdual.2,chartFiberInverse] using H

lemma quadratic_scalar_gradient {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f:E → ℝ} {p s:E} {A S:E →L[ℝ] E}
    (hf:HasQuadraticExpansion f p A) {φ:ℝ → ℝ} {l:ℝ}
    (hφ:HasDerivAt φ l (f 0))
    (hS:HasQuadraticExpansion (fun h=>φ (f h)) s S) : s=l • p := by
  have H:=hS.hasFDerivAt.unique (hφ.comp_hasFDerivAt 0 hf.hasFDerivAt)
  apply ext_inner_right ℝ
  intro d
  have HH:=congrArg (fun L:E →L[ℝ] ℝ=>L d) H
  simpa only [innerSL_apply_apply,smul_apply,smul_eq_mul,
    real_inner_smul_left] using HH

end WeakMTWTransport

end

end OAI
