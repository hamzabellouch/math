import OAI.Analysis.BernoulliCone.PrimitiveLocal

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
def bulkExpression (A:E×ℝ→E) (p:E×ℝ):ℝ:=
  divergence (fun x=>A (x,p.2)) p.1+inner ℝ (A p) (deriv (fun t=>A (p.1,t)) p.2)
lemma bulkExpression_congr {A B:E×ℝ→E} {p:E×ℝ} (he:A =ᶠ[𝓝 p] B) :
    bulkExpression A p=bulkExpression B p := by
  have hx:(fun x=>A (x,p.2)) =ᶠ[𝓝 p.1] (fun x=>B (x,p.2)):=
    he.comp_tendsto (continuousAt_id.prodMk continuousAt_const)
  have ht:(fun t=>A (p.1,t)) =ᶠ[𝓝 p.2] (fun t=>B (p.1,t)):=
    he.comp_tendsto (continuousAt_const.prodMk continuousAt_id)
  unfold bulkExpression divergence
  rw [hx.fderiv_eq,he.self_of_nhds,ht.deriv_eq]
end Bernoulli.Foliation

end
end

end OAI
