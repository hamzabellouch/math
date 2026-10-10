import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.SeparableReducingHull

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def generator (T : ι → H →L[ℂ] H) (i : ι × Bool) : H →L[ℂ] H :=
  if i.2 then star (T i.1) else T i.1

def orbit (T : ι → H →L[ℂ] H) (v : κ → H) (p : List (ι × Bool) × κ) : H :=
  (p.1.map (generator T)).prod (v p.2)

def hull (T : ι → H →L[ℂ] H) (v : κ → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (orbit T v))).topologicalClosure

lemma hull_closed (T : ι → H →L[ℂ] H) (v : κ → H) :
    IsClosed (hull T v : Set H) := Submodule.isClosed_topologicalClosure _

instance hull_complete (T : ι → H →L[ℂ] H) (v : κ → H) : CompleteSpace (hull T v) :=
  (hull_closed T v).completeSpace_coe

lemma vector_mem (T : ι → H →L[ℂ] H) (v : κ → H) (j : κ) : v j∈hull T v := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨([],j),by simp [orbit]⟩

lemma generator_invariant (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι × Bool) :
    ∀ x∈hull T v, generator T i x∈hull T v := by
  change (Submodule.span ℂ (Set.range (orbit T v))).topologicalClosure ≤
    (hull T v).comap (generator T i).toLinearMap
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨w,j⟩,rfl⟩
    change generator T i (orbit T v (w,j))∈hull T v
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨(i::w,j),by simp [orbit,mul_apply_eq_comp]⟩
  · exact (hull_closed T v).preimage (generator T i).continuous

lemma invariant (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι) :
    ∀ x∈hull T v,T i x∈hull T v := by
  simpa only [generator,Bool.false_eq_true,ite_false] using generator_invariant T v (i,false)

lemma star_invariant (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι) :
    ∀ x∈hull T v,star (T i) x∈hull T v := by
  simpa only [generator,ite_true] using generator_invariant T v (i,true)

instance hull_separable [Countable ι] [Countable κ]
    (T : ι → H →L[ℂ] H) (v : κ → H) : TopologicalSpace.SeparableSpace (hull T v) := by
  apply TopologicalSpace.IsSeparable.separableSpace
  exact ((Set.countable_range (orbit T v)).isSeparable.span (R := ℂ)).closure

def reducingAlgebra (K : Submodule ℂ H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | (∀ x∈K,T x∈K) ∧ (∀ x∈K,star T x∈K)}
  zero_mem' := by simp
  add_mem' := by
    rintro S T ⟨hS,hSs⟩ ⟨hT,hTs⟩
    constructor
    · intro x hx; exact K.add_mem (hS x hx) (hT x hx)
    · intro x hx; simpa only [star_add,add_apply] using K.add_mem (hSs x hx) (hTs x hx)
  mul_mem' := by
    rintro S T ⟨hS,hSs⟩ ⟨hT,hTs⟩
    constructor
    · intro x hx; exact hS _ (hT x hx)
    · intro x hx; simpa only [star_mul,mul_apply_eq_comp] using hTs _ (hSs x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx; simpa only [Algebra.algebraMap_eq_smul_one,smul_apply,
        one_apply_eq_self] using K.smul_mem c hx
    · intro x hx; simpa only [Algebra.algebraMap_eq_smul_one,star_smul,star_one,
        smul_apply,one_apply_eq_self] using K.smul_mem (star c) hx
  star_mem' := by rintro T ⟨hT,hTs⟩; exact ⟨hTs,by simpa only [star_star] using hT⟩

lemma reducingAlgebra_closed (K : Submodule ℂ H) (hK : IsClosed (K : Set H)) :
    IsClosed (reducingAlgebra K : Set (H →L[ℂ] H)) := by
  change IsClosed {T : H →L[ℂ] H | (∀ x∈K,T x∈K) ∧ (∀ x∈K,star T x∈K)}
  simp only [Set.ofPred_and,Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      hK.preimage (show Continuous (fun T : H →L[ℂ] H => T x) by fun_prop)))
  · exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      hK.preimage (show Continuous (fun T : H →L[ℂ] H => star T x) by fun_prop)))

lemma generator_mem_reducingAlgebra (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι) :
    T i∈reducingAlgebra (hull T v) := ⟨invariant T v i,star_invariant T v i⟩

lemma generated_reduces (T : ι → H →L[ℂ] H) (v : κ → H) :
    (StarAlgebra.adjoin ℂ (Set.range T)).topologicalClosure ≤ reducingAlgebra (hull T v) := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact generator_mem_reducingAlgebra T v i
  · exact reducingAlgebra_closed _ (hull_closed T v)

end Kadison.SeparableReducingHull

end

end
end

end OAI
