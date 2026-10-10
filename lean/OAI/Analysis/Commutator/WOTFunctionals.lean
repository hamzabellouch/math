import Mathlib
import OAI.Analysis.Commutator.FiniteSupportFactorization

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

open OperatorFunctionals

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coeffLM (p : H × StrongDual ℂ H) : (H →WOT[ℂ] H) →ₗ[ℂ] ℂ :=
  (LinearMap.proj p).comp (inducingFn (RingHom.id ℂ) H H)

omit [CompleteSpace H] in
@[simp] lemma coeffLM_apply (p : H × StrongDual ℂ H) (T : H →L[ℂ] H) :
    coeffLM p (ofCLM T)=p.2 (T p.1) := rfl

omit [CompleteSpace H] in
lemma wot_topology : (inferInstance : TopologicalSpace (H →WOT[ℂ] H))=
    ⨅ p : H × StrongDual ℂ H, TopologicalSpace.induced (coeffLM p) inferInstance := by
  change TopologicalSpace.induced (inducingFn (RingHom.id ℂ) H H) Pi.topologicalSpace=_
  rw [induced_to_pi]
  rfl

theorem factorization (φ : (H →WOT[ℂ] H) →L[ℂ] ℂ) :
    ∃ (n : ℕ) (x y : PiLp 2 (fun _ : Fin n => H)),
      (∀ T : H →L[ℂ] H, φ (ofCLM T)=∑ i, inner ℂ (y i) (T (x i))) ∧
        ‖x‖*‖y‖≤‖φ.comp ContinuousLinearMap.WOTofCLM‖ := by
  classical
  have hm : φ.toLinearMap ∈ Submodule.span ℂ (Set.range (coeffLM (H:=H))) := by
    apply (LinearMap.mem_span_iff_continuous _).mpr
    rw [←wot_topology]
    exact φ.continuous
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  let a : c.support → H := fun i => i.1.1
  let b : c.support → H := fun i => star (c i.1) • (InnerProductSpace.toDual ℂ H).symm i.1.2
  have he : φ.comp ContinuousLinearMap.WOTofCLM=finiteFunctional a b := by
    ext T
    change φ.toLinearMap (ofCLM T)=finiteFunctional a b T
    rw [←hc]
    simp only [Finsupp.sum,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      finiteFunctional_apply,coeffLM_apply]
    rw [←Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro i _
    simp [a,b,InnerProductSpace.toDual_symm_apply,mul_comm]
  obtain ⟨n,x,y,hxy,hn⟩ := exists_finite_support_factorization a b
  refine ⟨n,x,y,?_,?_⟩
  · intro T
    have hh := congrArg (fun f : StrongDual ℂ (H →L[ℂ] H) => f T) he
    exact hh.trans (hxy T)
  · rwa [he]

end Kadison.WOTDistance

end

end
end

end OAI
