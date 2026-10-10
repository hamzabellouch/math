import OAI.RepresentationTheory.RestrictedTilting.SpecializeCompletion

namespace OAI

namespace FiberFunctorProof
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (I : Ideal R)

attribute [local instance 1100] AdicCompletion.smul

lemma completion_self_smul (a b : AdicCompletion I R) : a • b = a * b := by
  apply AdicCompletion.ext
  intro n
  rw [AdicCompletion.smul_eval, AdicCompletion.val_mul]
  induction a.val n, b.val n using Quotient.inductionOn₂' with
  | h r s => rfl

lemma completion_map_add (F G : M →ₗ[R] N) (x : AdicCompletion I M) :
    AdicCompletion.map I (F+G) x = AdicCompletion.map I F x + AdicCompletion.map I G x := by
  apply AdicCompletion.ext
  intro n
  obtain ⟨v,hv⟩ := (I^n • (⊤ : Submodule R M)).mkQ_surjective (x.val n)
  simp only [AdicCompletion.map_val_apply]
  change (F+G).reduceModIdeal (I^n) (x.val n) =
    F.reduceModIdeal (I^n) (x.val n) + G.reduceModIdeal (I^n) (x.val n)
  rw [← hv]
  rfl

lemma completion_map_sum {ι : Type*} (s : Finset ι) (F : ι → M →ₗ[R] N)
    (x : AdicCompletion I M) :
    AdicCompletion.map I (∑ i ∈ s, F i) x = ∑ i ∈ s, AdicCompletion.map I (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, completion_map_add, ih]

lemma completion_map_smul (a : R) (F : M →ₗ[R] N) (x : AdicCompletion I M) :
    AdicCompletion.map I (a • F) x = algebraMap R (AdicCompletion I R) a • AdicCompletion.map I F x := by
  have he : a • F = (a • (LinearMap.id : N →ₗ[R] N)).comp F := rfl
  rw [he, ← AdicCompletion.map_comp_apply, completion_map_scalar]
end FiberFunctorProof

end OAI
