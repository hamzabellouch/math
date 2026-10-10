import OAI.Analysis.BernoulliCone.FoliationGraph

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma divergence_add {f g:E→E} {x:E}
    (hf:DifferentiableAt ℝ f x) (hg:DifferentiableAt ℝ g x) :
    divergence (fun y=>f y+g y) x=divergence f x+divergence g x := by
  have hd : fderiv ℝ (fun y=>f y+g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  rw [divergence,hd]
  simp only [add_apply,inner_add_right,Finset.sum_add_distrib,divergence]
lemma graphPotential_differentiableAt {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (graphPotential A u v) x := by
  have hd(w:E→ℝ)(hw:DifferentiableAt ℝ w x):
      DifferentiableAt ℝ (fun y:E=>ParametricIntegral.heightPrimitive A (y,w y)) x:=
    DifferentiableAt.comp (f:=fun y:E=>(y,w y)) (g:=ParametricIntegral.heightPrimitive A) x
      (ParametricIntegral.heightPrimitive_differentiable hA (x,w x)) (differentiableAt_id.prodMk hw)
  exact ((hd v hv).sub (hd u hu)).const_smul 2

def splitGraphPotential (A B:E×ℝ→E) (u w v:E→ℝ) (x:E):E:=
  graphPotential A u w x+graphPotential B w v x

/-- The moving seam contribution is derived from the two actual graph
primitives. The sign is exactly the extended calibration flux jump. -/
theorem split_graph_bound {A B:E×ℝ→E} (hA:ContDiff ℝ 1 A) (hB:ContDiff ℝ 1 B)
    {u w v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hw:DifferentiableAt ℝ w x)
    (hv:DifferentiableAt ℝ v x) (huw:u x≤w x) (hwv:w x≤v x)
    (hbulkA:∀s∈Icc (u x) (w x),divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0)
    (hbulkB:∀s∈Icc (w x) (v x),divergence (fun y:E=>B (y,s)) x+
      inner ℝ (B (x,s)) (deriv (fun t:ℝ=>B (x,t)) s)≤0)
    (hjump:‖B (x,w x)‖^2-‖A (x,w x)‖^2-
      2*inner ℝ (B (x,w x)-A (x,w x)) (gradient w x)≤0) :
    divergence (splitGraphPotential A B u w v) x≤‖gradient v x‖^2+
      ‖A (x,u x)‖^2-2*inner ℝ (A (x,u x)) (gradient u x) := by
  have hiA:=integrated_bulk hA x huw hbulkA
  have hiB:=integrated_bulk hB x hwv hbulkB
  have hs:0≤‖gradient v x-B (x,v x)‖^2:=sq_nonneg _
  rw [norm_sub_sq_real] at hs
  have he:inner ℝ (gradient v x) (B (x,v x))=inner ℝ (B (x,v x)) (gradient v x):=real_inner_comm _ _
  rw [he] at hs
  have hj:=hjump
  rw [inner_sub_left] at hj
  change divergence (fun y=>graphPotential A u w y+graphPotential B w v y) x ≤ _
  rw [divergence_add
    (graphPotential_differentiableAt hA hu hw) (graphPotential_differentiableAt hB hw hv),
    graph_potential_identity hA hu hw,graph_potential_identity hB hw hv]
  linarith
end Bernoulli.Foliation

end
end

end OAI
