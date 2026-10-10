import OAI.Analysis.BernoulliCone.ClampedSeam

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_eq_of_order_contact {u v:E→ℝ} {x:E}
    (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (hle:∀y,u y≤v y) (he:u x=v x) : gradient u x=gradient v x := by
  have hm:IsLocalMin (fun y=>v y-u y) x:=by
    filter_upwards [] with y
    change v x-u x≤v y-u y
    rw [←he,sub_self]
    exact sub_nonneg.mpr (hle y)
  have hh:=hm.hasFDerivAt_eq_zero (hv.hasFDerivAt.sub hu.hasFDerivAt)
  exact congrArg ((toDual ℝ E).symm) (sub_eq_zero.mp hh).symm

lemma graph_divergence_zero_contact {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (hle:∀y,u y≤v y) (he:u x=v x) : divergence (graphPotential A u v) x=0 := by
  rw [graph_potential_identity hA hu hv,he,gradient_eq_of_order_contact hu hv hle he]
  simp

lemma graph_potential_bulk_bound_open {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hv:DifferentiableAt ℝ v x)
    (huv:u x≤v x)
    (hbulk:∀s∈Ioo (u x) (v x),divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    divergence (graphPotential A u v) x≤‖gradient v x‖^2+
      ‖A (x,u x)‖^2-2*inner ℝ (A (x,u x)) (gradient u x) := by
  have hi:=integrated_bulk_open hA x huv hbulk
  have hs:0≤‖gradient v x-A (x,v x)‖^2:=sq_nonneg _
  have he:inner ℝ (gradient v x) (A (x,v x))=inner ℝ (A (x,v x)) (gradient v x):=real_inner_comm _ _
  rw [norm_sub_sq_real,he] at hs
  rw [graph_potential_identity hA hu hv]
  linarith

/-- The clamped primitive only needs a jump condition when the seam lies
strictly between the endpoint graphs. On contact sets the two gradients
agree, so the spurious branch cancels exactly. -/
lemma split_graph_bound_open {A B:E×ℝ→E} (hA:ContDiff ℝ 1 A) (hB:ContDiff ℝ 1 B)
    {u w v:E→ℝ} {x:E} (hu:DifferentiableAt ℝ u x) (hw:DifferentiableAt ℝ w x)
    (hv:DifferentiableAt ℝ v x) (huw:∀y,u y≤w y) (hwv:∀y,w y≤v y)
    (hbulkA:∀s∈Ioo (u x) (w x),divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0)
    (hbulkB:∀s∈Ioo (w x) (v x),divergence (fun y:E=>B (y,s)) x+
      inner ℝ (B (x,s)) (deriv (fun t:ℝ=>B (x,t)) s)≤0)
    (hjump:u x<w x → w x<v x → ‖B (x,w x)‖^2-‖A (x,w x)‖^2-
      2*inner ℝ (B (x,w x)-A (x,w x)) (gradient w x)≤0) :
    divergence (splitGraphPotential A B u w v) x≤‖gradient v x‖^2+
      ‖(if u x=w x then B else A) (x,u x)‖^2-
        2*inner ℝ ((if u x=w x then B else A) (x,u x)) (gradient u x) := by
  have hd:divergence (splitGraphPotential A B u w v) x=
      divergence (graphPotential A u w) x+divergence (graphPotential B w v) x:=
    divergence_add (graphPotential_differentiableAt hA hu hw) (graphPotential_differentiableAt hB hw hv)
  by_cases heu:u x=w x
  · rw [ite_eq_left heu,hd,graph_divergence_zero_contact hA hu hw huw heu,zero_add]
    have heG:=gradient_eq_of_order_contact hu hw huw heu
    simpa only [←heu,←heG] using graph_potential_bulk_bound_open hB hw hv (hwv x) hbulkB
  · rw [ite_eq_right heu]
    by_cases hev:w x=v x
    · rw [hd,graph_divergence_zero_contact hB hw hv hwv hev,add_zero]
      have heG:=gradient_eq_of_order_contact hw hv hwv hev
      simpa only [heG] using graph_potential_bulk_bound_open hA hu hw (huw x) hbulkA
    · have hiA:=integrated_bulk_open hA x (huw x) hbulkA
      have hiB:=integrated_bulk_open hB x (hwv x) hbulkB
      have hj:=hjump (lt_of_le_of_ne (huw x) heu) (lt_of_le_of_ne (hwv x) hev)
      rw [inner_sub_left] at hj
      have hs:0≤‖gradient v x-B (x,v x)‖^2:=sq_nonneg _
      have he:inner ℝ (gradient v x) (B (x,v x))=inner ℝ (B (x,v x)) (gradient v x):=real_inner_comm _ _
      rw [norm_sub_sq_real,he] at hs
      rw [hd,graph_potential_identity hA hu hw,graph_potential_identity hB hw hv]
      linarith
end Bernoulli.Foliation

end
end

end OAI
