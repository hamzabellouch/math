import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TupleChartDomain

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PointwisePolygonTables

variable {a m : ℕ}

noncomputable def conditionalAlternatingHom (U : polygonAlgebra a) :
    alternatingGroup (Fin m) →* polygonAlternatingGroup a m :=
  ((conditionalHom U).comp (alternatingGroup (Fin m)).subtype).codRestrict
    (polygonAlternatingGroup a m) (fun s => conditionalHom_alternating_mem U s.property)

theorem conditionalHom_disjoint_commute (U V : polygonAlgebra a)
    (hUV : Disjoint U.val V.val) (σ ρ : Equiv.Perm (Fin m)) :
    Commute (conditionalHom U σ) (conditionalHom V ρ) := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm U σ (conditionalPerm V ρ p) =
    conditionalPerm V ρ (conditionalPerm U σ p)
  by_cases hu : p.2 ∈ U.val <;> by_cases hv : p.2 ∈ V.val
  · exact False.elim (Set.disjoint_left.mp hUV hu hv)
  all_goals simp [conditionalPerm, hu, hv]

structure PolygonLabelling (a : ℕ) (Ω : Type*) where
  label : GenericSquare a → Ω
  fiber_mem : ∀ ω, {p | label p = ω} ∈ polygonAlgebra a

noncomputable def PolygonLabelling.fiber {Ω : Type*} (v : PolygonLabelling a Ω)
    (ω : Ω) : polygonAlgebra a := ⟨{p | v.label p = ω},v.fiber_mem ω⟩

theorem PolygonLabelling.fiber_disjoint {Ω : Type*} (v : PolygonLabelling a Ω)
    {ω ν : Ω} (h : ω ≠ ν) : Disjoint (v.fiber ω).val (v.fiber ν).val := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact h (hp.symm.trans hq)

noncomputable def PolygonLabelling.permutationHom {Ω : Type*} (v : PolygonLabelling a Ω) :
    (Ω → alternatingGroup (Fin m)) →* Equiv.Perm (TrackPoint a m) where
  toFun σ := {
    toFun := fun p => ((σ (v.label p.2)).val p.1,p.2)
    invFun := fun p => ((σ (v.label p.2)).val.symm p.1,p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  map_one' := by apply Equiv.ext; intro p; rfl
  map_mul' := by intro σ ρ; apply Equiv.ext; intro p; rfl

@[simp] theorem PolygonLabelling.permutationHom_apply {Ω : Type*}
    (v : PolygonLabelling a Ω) (σ : Ω → alternatingGroup (Fin m)) (p : TrackPoint a m) :
    v.permutationHom σ p = ((σ (v.label p.2)).val p.1,p.2) := rfl

noncomputable def PolygonLabelling.tableHom {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) :
    (Ω → alternatingGroup (Fin m)) →* polygonAlternatingGroup a m :=
  MonoidHom.noncommPiCoprod (fun ω => conditionalAlternatingHom (v.fiber ω)) (by
    intro ω ν h s t
    change _ * _ = _ * _
    apply Subtype.ext
    exact (conditionalHom_disjoint_commute (v.fiber ω) (v.fiber ν)
      (v.fiber_disjoint h) s.val t.val).eq)

@[simp] theorem PolygonLabelling.tableHom_single {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (v : PolygonLabelling a Ω) (ω : Ω) (s : alternatingGroup (Fin m)) :
    v.tableHom (Pi.mulSingle ω s) = conditionalAlternatingHom (v.fiber ω) s :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

theorem PolygonLabelling.tableHom_permutation {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) :
    (polygonFullGroup a m).subtype.comp
        ((polygonAlternatingGroup a m).subtype.comp v.tableHom) = v.permutationHom := by
  classical
  apply MonoidHom.pi_ext
  intro ω s
  simp only [MonoidHom.comp_apply, v.tableHom_single]
  apply Equiv.ext
  intro p
  change conditionalPerm (v.fiber ω) s.val p =
    (((Pi.mulSingle ω s : Ω → alternatingGroup (Fin m)) (v.label p.2)).val p.1,p.2)
  by_cases hp : v.label p.2 = ω
  · simp [conditionalPerm, PolygonLabelling.fiber, hp]
  · simp [conditionalPerm, PolygonLabelling.fiber, hp]

@[simp] theorem PolygonLabelling.tableHom_apply {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) (σ : Ω → alternatingGroup (Fin m)) (p : TrackPoint a m) :
    (v.tableHom σ).val.val p = ((σ (v.label p.2)).val p.1,p.2) := by
  have he := DFunLike.congr_fun v.tableHom_permutation σ
  exact DFunLike.congr_fun he p

theorem PolygonLabelling.tableHom_injective {Ω : Type*} [Fintype Ω]
    (v : PolygonLabelling a Ω) (hv : Function.Surjective v.label) :
    Function.Injective (v.tableHom (m := m)) := by
  intro s t h
  funext ω
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨p,hp⟩ := hv ω
  have he := congrArg (fun g : polygonAlternatingGroup a m => g.val.val (i,p)) h
  simpa only [v.tableHom_apply, hp] using congrArg Prod.fst he

noncomputable def polygonAssignment {ι : Type*} (U : ι → polygonAlgebra a)
    (p : GenericSquare a) : ι → Bool := by
  classical
  exact fun i => decide (p ∈ (U i).val)

theorem polygonAssignment_fiber_mem {ι : Type*} [Finite ι]
    (U : ι → polygonAlgebra a) (ω : ι → Bool) :
    {p | polygonAssignment U p = ω} ∈ polygonAlgebra a := by
  classical
  have he : {p | polygonAssignment U p = ω} =
      ⋂ i, if ω i then (U i).val else (U i).valᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff, polygonAssignment]
    apply forall_congr'
    intro i
    cases ω i <;> simp
  rw [he]
  apply BooleanSubalgebra.iInf_mem
  intro i
  cases ω i
  · exact BooleanSubalgebra.compl_mem (U i).property
  · exact (U i).property

noncomputable def actualPolygonLabelling {ι : Type*} [Finite ι]
    (U : ι → polygonAlgebra a) : PolygonLabelling a (Set.range (polygonAssignment U)) where
  label p := ⟨polygonAssignment U p,⟨p,rfl⟩⟩
  fiber_mem ω := by
    have he : {p | (⟨polygonAssignment U p,⟨p,rfl⟩⟩ : Set.range (polygonAssignment U)) = ω} =
        {p | polygonAssignment U p = ω.val} := by
      ext p
      exact Subtype.ext_iff
    rw [he]
    exact polygonAssignment_fiber_mem U ω.val

theorem actualPolygonLabelling_surjective {ι : Type*} [Finite ι]
    (U : ι → polygonAlgebra a) : Function.Surjective (actualPolygonLabelling U).label := by
  rintro ⟨ω,p,rfl⟩
  exact ⟨p,rfl⟩

end PointwisePolygonTables

end SimpleAmenable
end
end

end OAI
