import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit

namespace OAI

noncomputable section

noncomputable section

open scoped InnerProductSpace Topology

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cornerOrbit (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (p : H →L[ℂ] H) (ξ : H) : Submodule ℂ H where
  carrier := {x | ∃ a : H →L[ℂ] H, a ∈ S ∧ p*a=a ∧ a*p=a ∧ a ξ=x}
  zero_mem' := ⟨0,S.zero_mem,by simp,by simp,by simp⟩
  add_mem' := by
    rintro x y ⟨a,ha,hpa,hap,rfl⟩ ⟨b,hb,hpb,hbp,rfl⟩
    exact ⟨a+b,S.add_mem ha hb,by rw [mul_add,hpa,hpb],by rw [add_mul,hap,hbp],rfl⟩
  smul_mem' := by
    rintro c x ⟨a,ha,hpa,hap,rfl⟩
    exact ⟨c • a,S.smul_mem ha c,by rw [mul_smul_comm,hpa],by rw [smul_mul_assoc,hap],rfl⟩

theorem mem_cornerOrbit_closure_iff (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {p : H →L[ℂ] H} (hp : p*p=p) (hpS : p∈S) {ξ : H} (hξ : p ξ=ξ) (x : H) :
    x∈(cornerOrbit S p ξ).topologicalClosure ↔ x∈cyclicSubspace S ξ ∧ p x=x := by
  constructor
  · intro hx
    have hsub : (cornerOrbit S p ξ).topologicalClosure ≤ cyclicSubspace S ξ := by
      apply Submodule.topologicalClosure_minimal
      · rintro y ⟨a,ha,_,_,rfl⟩
        exact (orbitSubmodule S ξ).le_topologicalClosure ⟨a,ha,rfl⟩
      · exact (orbitSubmodule S ξ).isClosed_topologicalClosure
    refine ⟨hsub hx, ?_⟩
    apply closure_minimal (t := {y | p y=y}) ?_ (isClosed_eq p.continuous continuous_id) hx
    rintro y ⟨a,_,hpa,_,rfl⟩
    exact congrArg (fun T : H →L[ℂ] H => T ξ) hpa
  · rintro ⟨hx,hpx⟩
    have hclosed := (cornerOrbit S p ξ).isClosed_topologicalClosure.preimage p.continuous
    have hmem : p x∈(cornerOrbit S p ξ).topologicalClosure := by
      apply closure_minimal (t := {y | p y∈(cornerOrbit S p ξ).topologicalClosure}) ?_ hclosed hx
      rintro y ⟨a,ha,rfl⟩
      apply (cornerOrbit S p ξ).le_topologicalClosure
      refine ⟨p*a*p,S.mul_mem (S.mul_mem hpS ha) hpS,?_,?_,?_⟩
      · rw [←mul_assoc,←mul_assoc,hp]
      · rw [mul_assoc (p*a),hp]
      · change p (a (p ξ))=p (a ξ)
        rw [hξ]
    rwa [hpx] at hmem

lemma cyclicSubspace_reduces (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    {a : H →L[ℂ] H} (ha : a∈S) :
    (cyclicSubspace S ξ).starProjection*a=a*(cyclicSubspace S ξ).starProjection :=
  projection_commutes_of_invariant _ a (cyclicSubspace_invariant S ξ ha)
    (cyclicSubspace_invariant S ξ (star_mem ha))

end Kadison
end
end

end OAI
