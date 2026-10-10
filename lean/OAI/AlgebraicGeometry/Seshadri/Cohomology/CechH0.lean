import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CechPresentation

namespace OAI


                                
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

private def presentationConnectingMap
    (projection : P →ₗ[K] M) (sourceA sourceB sourceC : Submodule K P)
    (target : Submodule K M)
    (liftAB : target →ₗ[K] ↥(sourceA ⊓ sourceB))
    (liftAC : target →ₗ[K] ↥(sourceA ⊓ sourceC))
    (liftBC : target →ₗ[K] ↥(sourceB ⊓ sourceC))
    (mapAB : ∀ sectionValue, projection (liftAB sectionValue) = sectionValue)
    (mapAC : ∀ sectionValue, projection (liftAC sectionValue) = sectionValue)
    (mapBC : ∀ sectionValue, projection (liftBC sectionValue) = sectionValue) :
    target →ₗ[K] cycles (sourceA.comap projection.ker.subtype)
      (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype) where
  toFun sectionValue :=
    ⟨(⟨⟨(liftAB sectionValue : P) - liftAC sectionValue, by
          change projection _ = 0
          rw [map_sub, mapAB, mapAC, sub_self]⟩,
        sourceA.sub_mem (liftAB sectionValue).2.1 (liftAC sectionValue).2.1⟩,
      ⟨⟨(liftBC sectionValue : P) - liftAB sectionValue, by
          change projection _ = 0
          rw [map_sub, mapBC, mapAB, sub_self]⟩,
        sourceB.sub_mem (liftBC sectionValue).2.1 (liftAB sectionValue).2.2⟩,
      ⟨⟨(liftAC sectionValue : P) - liftBC sectionValue, by
          change projection _ = 0
          rw [map_sub, mapAC, mapBC, sub_self]⟩,
        sourceC.sub_mem (liftAC sectionValue).2.2 (liftBC sectionValue).2.2⟩), by
      apply Subtype.ext
      change ((liftAB sectionValue : P) - liftAC sectionValue) +
        ((liftBC sectionValue : P) - liftAB sectionValue) +
        ((liftAC sectionValue : P) - liftBC sectionValue) = 0
      abel⟩
  map_add' := by intros; ext <;> simp <;> abel
  map_smul' := by intros; ext <;> simp [smul_sub]

private theorem presentationConnectingMap_exact
    (projection : P →ₗ[K] M) (sourceA sourceB sourceC : Submodule K P)
    (target : Submodule K M)
    (liftAB : target →ₗ[K] ↥(sourceA ⊓ sourceB))
    (liftAC : target →ₗ[K] ↥(sourceA ⊓ sourceC))
    (liftBC : target →ₗ[K] ↥(sourceB ⊓ sourceC))
    (mapAB : ∀ sectionValue, projection (liftAB sectionValue) = sectionValue)
    (mapAC : ∀ sectionValue, projection (liftAC sectionValue) = sectionValue)
    (mapBC : ∀ sectionValue, projection (liftBC sectionValue) = sectionValue)
    (sectionValue : target)
    (boundary : presentationConnectingMap projection sourceA sourceB sourceC target
      liftAB liftAC liftBC mapAB mapAC mapBC sectionValue ∈
        fullBoundaries (sourceA.comap projection.ker.subtype)
          (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype)) :
    ∃ liftValue : ↥((sourceA ⊓ sourceB) ⊓ sourceC),
      projection liftValue = sectionValue := by
  let kernelA := sourceA.comap projection.ker.subtype
  let kernelB := sourceB.comap projection.ker.subtype
  let kernelC := sourceC.comap projection.ker.subtype
  obtain ⟨sumAB, hsumAB, valueC, hvalueC, sum_eq⟩ := Submodule.mem_sup.mp boundary
  obtain ⟨valueA, hvalueA, valueB, hvalueB, sumAB_eq⟩ := Submodule.mem_sup.mp hsumAB
  obtain ⟨boundaryAB, rfl⟩ := hvalueA
  obtain ⟨boundaryAC, rfl⟩ := hvalueB
  obtain ⟨boundaryBC, rfl⟩ := hvalueC
  have cycle_eq : edgeAB kernelA kernelB kernelC boundaryAB +
      edgeAC kernelA kernelB kernelC boundaryAC + edgeBC kernelA kernelB kernelC boundaryBC =
      presentationConnectingMap projection sourceA sourceB sourceC target
        liftAB liftAC liftBC mapAB mapAC mapBC sectionValue := by
    rw [sumAB_eq]
    exact sum_eq
  have component_eq : -(boundaryAB.val.val : P) + boundaryBC.val.val =
      (liftBC sectionValue : P) - liftAB sectionValue := by
    have equality := congrArg (fun cycle : cycles kernelA kernelB kernelC =>
      (cycle.val.2.1.val.val : P)) cycle_eq
    change -(boundaryAB.val.val : P) + 0 + boundaryBC.val.val =
      (liftBC sectionValue : P) - liftAB sectionValue at equality
    simpa only [add_zero] using equality
  have lift_eq : (liftAB sectionValue : P) - boundaryAB.val.val =
      (liftBC sectionValue : P) - boundaryBC.val.val := by
    calc
      _ = (liftBC sectionValue : P) - ((liftBC sectionValue : P) -
        liftAB sectionValue) - boundaryAB.val.val := by abel
      _ = _ := by rw [← component_eq]; abel
  have lift_mem : (liftAB sectionValue : P) - boundaryAB.val.val ∈
      (sourceA ⊓ sourceB) ⊓ sourceC := by
    refine ⟨⟨sourceA.sub_mem (liftAB sectionValue).2.1 boundaryAB.2.1,
      sourceB.sub_mem (liftAB sectionValue).2.2 boundaryAB.2.2⟩, ?_⟩
    rw [lift_eq]
    exact sourceC.sub_mem (liftBC sectionValue).2.2 boundaryBC.2.2
  refine ⟨⟨(liftAB sectionValue : P) - boundaryAB.val.val, lift_mem⟩, ?_⟩
  change projection ((liftAB sectionValue : P) - boundaryAB.val.val) = (sectionValue : M)
  rw [map_sub, mapAB, show projection (boundaryAB.val.val : P) = 0 from boundaryAB.val.2,
    sub_zero]

private theorem exists_presentationLift
    (projection : P →ₗ[K] M) (source : Submodule K P) (target common : Submodule K M)
    (map_mem : ∀ value ∈ source, projection value ∈ target)
    (surjective : ∀ value ∈ target, ∃ liftValue ∈ source, projection liftValue = value)
    (common_le : common ≤ target) :
    ∃ liftMap : common →ₗ[K] source, ∀ value, projection (liftMap value) = value := by
  let restricted : source →ₗ[K] target :=
    (projection.domRestrict source).codRestrict target (fun value => map_mem value value.2)
  have restricted_surjective : Function.Surjective restricted := by
    rintro ⟨value, value_mem⟩
    obtain ⟨liftValue, lift_mem, lift_eq⟩ := surjective value value_mem
    exact ⟨⟨liftValue, lift_mem⟩, Subtype.ext lift_eq⟩
  obtain ⟨inverse, inverse_eq⟩ := restricted.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr restricted_surjective)
  refine ⟨inverse.comp (Submodule.inclusion common_le), fun value => ?_⟩
  exact congrArg Subtype.val
    (LinearMap.congr_fun inverse_eq ⟨value, common_le value.2⟩)

private theorem finite_of_boundary_lift
    {source target middle : Type*}
    [AddCommGroup source] [Module K source] [Module.Finite K source]
    [AddCommGroup target] [Module K target] [AddCommGroup middle] [Module K middle]
    (boundary : Submodule K middle) [Module.Finite K (middle ⧸ boundary)]
    (connecting : target →ₗ[K] middle) (globalMap : source →ₗ[K] target)
    (exactness : ∀ sectionValue, connecting sectionValue ∈ boundary →
      sectionValue ∈ globalMap.range) : Module.Finite K target := by
  let : Module.Finite K (target ⧸ globalMap.range) := by
    apply finite_quotient_of_kernel_le (boundary.mkQ.comp connecting) globalMap.range
    intro sectionValue kernel_mem
    exact exactness sectionValue ((Submodule.Quotient.mk_eq_zero boundary).mp kernel_mem)
  exact Module.Finite.of_submodule_quotient globalMap.range

private theorem finite_presentationTarget
    (projection : P →ₗ[K] M) (sourceA sourceB sourceC : Submodule K P)
    (target : Submodule K M)
    (liftAB : target →ₗ[K] ↥(sourceA ⊓ sourceB))
    (liftAC : target →ₗ[K] ↥(sourceA ⊓ sourceC))
    (liftBC : target →ₗ[K] ↥(sourceB ⊓ sourceC))
    (mapAB : ∀ sectionValue, projection (liftAB sectionValue) = sectionValue)
    (mapAC : ∀ sectionValue, projection (liftAC sectionValue) = sectionValue)
    (mapBC : ∀ sectionValue, projection (liftBC sectionValue) = sectionValue)
    (globalMap : ↥((sourceA ⊓ sourceB) ⊓ sourceC) →ₗ[K] target)
    (globalMap_eq : ∀ sectionValue, (globalMap sectionValue : M) = projection sectionValue)
    [Module.Finite K ↥((sourceA ⊓ sourceB) ⊓ sourceC)]
    [Module.Finite K (@HasQuotient.Quotient _ _
      (Submodule.hasQuotient (R := K) (M := cycles (sourceA.comap projection.ker.subtype)
        (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype)))
      (fullBoundaries (sourceA.comap projection.ker.subtype)
        (sourceB.comap projection.ker.subtype) (sourceC.comap projection.ker.subtype)))] :
    Module.Finite K target := by
  let kernelA := sourceA.comap projection.ker.subtype
  let kernelB := sourceB.comap projection.ker.subtype
  let kernelC := sourceC.comap projection.ker.subtype
  let connecting : target →ₗ[K] cycles kernelA kernelB kernelC :=
    presentationConnectingMap projection sourceA sourceB sourceC target
      liftAB liftAC liftBC mapAB mapAC mapBC
  let boundary := fullBoundaries kernelA kernelB kernelC
  apply finite_of_boundary_lift (source := ↥((sourceA ⊓ sourceB) ⊓ sourceC))
    (target := target) (middle := cycles kernelA kernelB kernelC) boundary connecting globalMap
  intro sectionValue boundary_mem
  obtain ⟨liftValue, lift_eq⟩ := presentationConnectingMap_exact
    projection sourceA sourceB sourceC target liftAB liftAC liftBC
      mapAB mapAC mapBC sectionValue boundary_mem
  exact ⟨liftValue, Subtype.ext ((globalMap_eq liftValue).trans lift_eq)⟩

theorem finite_H0_of_presentation
    (f : P →ₗ[K] M) (A B C : Submodule K P) (V : Fin 3 → Submodule K M)
    (h0 : ∀ x ∈ A ⊓ B, f x ∈ V 0) (h1 : ∀ x ∈ A ⊓ C, f x ∈ V 1)
    (h2 : ∀ x ∈ B ⊓ C, f x ∈ V 2)
    (sur0 : ∀ x ∈ V 0, ∃ y ∈ A ⊓ B, f y = x)
    (sur1 : ∀ x ∈ V 1, ∃ y ∈ A ⊓ C, f y = x)
    (sur2 : ∀ x ∈ V 2, ∃ y ∈ B ⊓ C, f y = x)
    [Module.Finite K ↥((A ⊓ B) ⊓ C)]
    [Module.Finite K (@HasQuotient.Quotient _ _
      (Submodule.hasQuotient (R := K) (M := cycles (A.comap f.ker.subtype)
        (B.comap f.ker.subtype) (C.comap f.ker.subtype)))
      (fullBoundaries (K := K) (A.comap f.ker.subtype)
        (B.comap f.ker.subtype) (C.comap f.ker.subtype)))] :
    Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2) := by
  let Z := (V 0 ⊓ V 1) ⊓ V 2
  obtain ⟨l0, e0⟩ := exists_presentationLift f (A ⊓ B) (V 0) Z h0 sur0
    (inf_le_left.trans inf_le_left)
  obtain ⟨l1, e1⟩ := exists_presentationLift f (A ⊓ C) (V 1) Z h1 sur1
    (inf_le_left.trans inf_le_right)
  obtain ⟨l2, e2⟩ := exists_presentationLift f (B ⊓ C) (V 2) Z h2 sur2 inf_le_right
  let f0 : ↥((A ⊓ B) ⊓ C) →ₗ[K] Z :=
    (f.domRestrict _).codRestrict Z (fun x =>
      ⟨⟨h0 x x.2.1,h1 x ⟨x.2.1.1,x.2.2⟩⟩,h2 x ⟨x.2.1.2,x.2.2⟩⟩)
  exact finite_presentationTarget f A B C Z l0 l1 l2 e0 e1 e2 f0 (fun _ => rfl)
end
end MaximalSeshadri.PlaneCech

end

end OAI
