import OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity
import OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem reducedComponentι_range (X : Scheme.{0}) (C : irreducibleComponents X) :
    Set.range (reducedComponentι X C) = C.val := by
  let Z : Closeds X := ⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  exact I.range_subschemeι.trans (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

theorem reducedComponentι_mem (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) : reducedComponentι X C z ∈ C.val := by
  rw [← reducedComponentι_range]
  exact ⟨z,rfl⟩

theorem reducedComponentι_genericPoint (X : Scheme.{0}) (C : irreducibleComponents X) :
    reducedComponentι X C (genericPoint (reducedComponent X C)) =
      (genericPoints.ofComponent C).val := by
  have hgen : IsGenericPoint
      (reducedComponentι X C (genericPoint (reducedComponent X C))) C.val := by
    change closure {_} = C.val
    rw [← Set.image_singleton, (reducedComponentι X C).isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, reducedComponentι_range]
  exact hgen.eq (genericPoints.isGenericPoint_ofComponent C)

theorem fromSpecStalk_bot_eq_genericPoint (Y : Scheme.{0}) [IsIntegral Y] (z : Y) :
    Y.fromSpecStalk z (⟨⊥,inferInstance⟩ : Spec (Y.presheaf.stalk z)) = genericPoint Y := by
  have hbot : (⊥ : Ideal (Y.presheaf.stalk z)) ∈ minimalPrimes (Y.presheaf.stalk z) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  have hgen := (generic_embedding_iff (Y.fromSpecStalk z).isEmbedding
    (fromSpecStalk_generizing Y z) (⟨⊥,inferInstance⟩ : Spec (Y.presheaf.stalk z))).mp
      (minimalPrimesGenericEquiv (Y.presheaf.stalk z) ⟨⊥,hbot⟩).property
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hgen

def reducedComponentStalkPrime (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) : minimalPrimes (X.presheaf.stalk (reducedComponentι X C z)) :=
  (stalkMinimalPrimesEquivComponentsThrough X (reducedComponentι X C z)).symm
    ⟨C,reducedComponentι_mem X C z⟩

theorem reducedComponentι_stalkMap_ker (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) :
    RingHom.ker ((reducedComponentι X C).stalkMap z).hom =
      (reducedComponentStalkPrime X C z).val := by
  let i := reducedComponentι X C
  let q : Spec (X.presheaf.stalk (i z)) :=
    ⟨RingHom.ker (i.stalkMap z).hom, RingHom.ker_isPrime _⟩
  let P := reducedComponentStalkPrime X C z
  have hq : X.fromSpecStalk (i z) q = (genericPoints.ofComponent C).val := by
    have hnat := congrArg (fun f : Spec ((reducedComponent X C).presheaf.stalk z) ⟶ X =>
      f (⟨⊥,inferInstance⟩ : Spec ((reducedComponent X C).presheaf.stalk z)))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := i) (x := z))
    change X.fromSpecStalk (i z) q =
      i ((reducedComponent X C).fromSpecStalk z (⟨⊥,inferInstance⟩ :
        Spec ((reducedComponent X C).presheaf.stalk z))) at hnat
    rw [hnat, fromSpecStalk_bot_eq_genericPoint]
    exact reducedComponentι_genericPoint X C
  have hP : X.fromSpecStalk (i z) (⟨P.val,P.property.1.1⟩ : Spec (X.presheaf.stalk (i z))) =
      (genericPoints.ofComponent C).val := by
    simpa only [P,i,reducedComponentStalkPrime,Equiv.apply_symm_apply] using
      stalkMinimalPrimesEquivComponentsThrough_point X (i z) P
  exact congrArg PrimeSpectrum.asIdeal
    ((X.fromSpecStalk (i z)).isEmbedding.injective (hq.trans hP.symm))

def reducedComponentStalkQuotientEquiv (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) :
    (X.presheaf.stalk (reducedComponentι X C z)) ⧸
      (reducedComponentStalkPrime X C z).val ≃+*
        (reducedComponent X C).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (reducedComponentι_stalkMap_ker X C z).symm).trans
    (((reducedComponentι X C).stalkMap z).hom.quotientKerEquivOfSurjective
      ((reducedComponentι X C).stalkMap_surjective z))

@[simp]
theorem reducedComponentStalkQuotientEquiv_mk (X : Scheme.{0})
    (C : irreducibleComponents X) (z : reducedComponent X C)
    (a : X.presheaf.stalk (reducedComponentι X C z)) :
    reducedComponentStalkQuotientEquiv X C z
      (Ideal.Quotient.mk (reducedComponentStalkPrime X C z).val a) =
        (reducedComponentι X C).stalkMap z a := by
  simp only [reducedComponentStalkQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem reducedComponentι_stalkMap_ne_zero (X : Scheme.{0})
    (C : irreducibleComponents X) (z : reducedComponent X C)
    (a : X.presheaf.stalk (reducedComponentι X C z)) (ha : a ∈ nonZeroDivisors _) :
    (reducedComponentι X C).stalkMap z a ≠ 0 := by
  intro h
  have hmem : a ∈ (reducedComponentStalkPrime X C z).val := by
    rw [← reducedComponentι_stalkMap_ker]
    exact h
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    hmem (reducedComponentStalkPrime X C z).property ha

end
end PiExponent.CurveCycle

end OAI
