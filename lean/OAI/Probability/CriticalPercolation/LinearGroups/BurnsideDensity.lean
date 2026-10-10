import Mathlib

namespace OAI

section
noncomputable section
open Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth

lemma toModuleEnd_surjective_of_simple {K A V : Type*} [Field K] [IsAlgClosed K]
    [Ring A] [Algebra K A] [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower K A V] [IsSimpleModule A V] [FiniteDimensional K V] :
    Surjective (Module.toModuleEnd K (S:=A) V) := by
  let E := Module.End A V
  have he : Surjective (algebraMap K E) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K).2
  let : Module.Finite E V := Module.Finite.of_restrictScalars_finite K E V
  intro T
  let T' : Module.End E V := {
    toFun := T
    map_add' := T.map_add
    map_smul' := by
      intro e x
      obtain ⟨c,rfl⟩ := he e
      change T (c • x)=c • T x
      exact T.map_smul c x }
  obtain ⟨a,ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R:=A) (M:=V) T'
  refine ⟨a,?_⟩
  ext x
  exact congrArg (fun f : Module.End E V => f x) ha

lemma subalgebra_eq_top_of_simple {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : Subalgebra K (Module.End K V))
    [IsSimpleModule A V] : A=⊤ := by
  apply top_unique
  intro T _
  obtain ⟨a,ha⟩ := toModuleEnd_surjective_of_simple (K:=K) (A:=A) (V:=V) T
  have he : (a : Module.End K V)=T := by
    ext v
    exact congrArg (fun f : Module.End K V => f v) ha
  exact he ▸ a.property

end CriticalPercolation.LinearGrowth
end
end

end OAI
