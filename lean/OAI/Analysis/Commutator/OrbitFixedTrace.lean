import Mathlib
import OAI.Analysis.Commutator.NormSeparableFixedPoint
import OAI.Analysis.Commutator.OrbitStateHull
import OAI.Analysis.Commutator.UnitaryDualAction

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.OrbitStateHull

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

lemma act_vector (u : unitary M) (x : H) :
    u • (vector M x).toWeakDual=(vector M (((u:M):H →L[ℂ] H) x)).toWeakDual := by
  apply UnitaryDualAction.weak_ext
  intro a
  change inner ℂ x ((star ((u:M):H →L[ℂ] H)) (((a:M):H →L[ℂ] H) (((u:M):H →L[ℂ] H) x))) =
    inner ℂ (((u:M):H →L[ℂ] H) x) (((a:M):H →L[ℂ] H) (((u:M):H →L[ℂ] H) x))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

lemma orbit_invariant (x : H) : CompactInvariant.Invariant (G:=unitary M) (orbit M x) := by
  intro u f hf
  obtain ⟨v,hv,rfl⟩ := hf
  let w : unitary (H →L[ℂ] H) := ⟨((u:M):H →L[ℂ] H),by
    constructor
    · exact congrArg (fun a : M => (a:H →L[ℂ] H)) u.property.1
    · exact congrArg (fun a : M => (a:H →L[ℂ] H)) u.property.2⟩
  refine ⟨w*v,M.mul_mem (u:M).property hv,?_⟩
  exact act_vector M u ((v:H →L[ℂ] H) x)

lemma hull_invariant (x : H) : CompactInvariant.Invariant (G:=unitary M) (hull M x) := by
  intro u f hf
  obtain ⟨L,hL⟩ := UnitaryDualAction.act_linear u
  have hLcont : Continuous L := by
    have he : (L : WeakDual ℂ M → WeakDual ℂ M)=(fun f => u • f) := funext hL
    rw [he]
    exact continuous_const_smul u
  have hmap : L '' convexHull ℝ (orbit M x) ⊆ convexHull ℝ (orbit M x) := by
    rw [L.image_convexHull]
    apply convexHull_mono
    rintro _ ⟨g,hg,rfl⟩
    rw [hL]
    exact orbit_invariant M x u g hg
  have hpre : closure (convexHull ℝ (orbit M x)) ⊆ L ⁻¹' closure (convexHull ℝ (orbit M x)) :=
    closure_minimal (fun g hg => subset_closure (hmap ⟨g,hg,rfl⟩))
      (isClosed_closure.preimage hLcont)
  have he := hpre hf
  change L f∈hull M x at he
  rwa [hL] at he

theorem exists_tracial_hull_of_norm_separable (x : H)
    (hsep : TopologicalSpace.IsSeparable (WeakDual.toStrongDual '' hull M x)) :
    ∃ f : WeakDual ℂ M, f∈hull M x ∧ ∀ a b : M,f (a*b)=f (b*a) := by
  let j : WeakDual ℂ M ≃ₗ[ℝ] StrongDual ℂ M :=
    { toFun := WeakDual.toStrongDual
      invFun := StrongDual.toWeakDual
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Continuous j.symm := by
    apply WeakDual.continuous_of_continuous_eval
    intro a
    change Continuous (fun f : StrongDual ℂ M => f a)
    exact (ContinuousLinearMap.apply ℂ ℂ a).continuous
  have hb : ∀ y : StrongDual ℂ M,∀ r : ℝ,IsClosed {f : WeakDual ℂ M | dist (j f) y≤r} := by
    intro y r
    change IsClosed (WeakDual.toStrongDual ⁻¹' Metric.closedBall y r)
    exact WeakDual.isClosed_closedBall y r
  obtain ⟨f,hf,hfix⟩ := CompactInvariant.exists_fixed_point j hj hb
    (fun u f g => UnitaryDualAction.act_dist u f g) (hull_compact M x)
    (hull_nonempty M x) (WeakDualHull.convex_hull (orbit M x)) (hull_invariant M x) hsep
  exact ⟨f,hf,UnitaryDualAction.trace_of_fixed f hfix⟩

end Kadison.OrbitStateHull

end

end
end

end OAI
