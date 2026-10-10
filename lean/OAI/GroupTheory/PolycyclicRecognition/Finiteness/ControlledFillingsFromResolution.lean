import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledEquivariantMaps
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledCycleFillings
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # Finite resolution terms give uniformly controlled fillings

Comparison with the homogeneous resolution provides the filler. Finite
generation bounds the image of the filling term, and equivariance bounds the
chain homotopy on each input scale.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {G : Type} [Group G] {n : ℕ}

theorem controlledCycleFillings_of_resolution
    (P : ProjectiveResolution (trivialIntegral G))
    (hfin : IntegralRepresentationFinite G (P.complex.X (n + 2))) :
    HasControlledCycleFillings ℤ G n := by
  let Q := Rep.standardResolution ℤ G
  let e := ProjectiveResolution.homotopyEquiv Q P
  let h := e.homotopyHomInvId.symm
  intro S hS
  obtain ⟨T, hT, hα⟩ := finiteRepresentation_range_controlled
    (P.complex.X (n + 2)) hfin (e.inv.f (n + 2))
  obtain ⟨U, hU, hh⟩ := equivariant_controlledChainImage
    (h.hom (n + 1) (n + 2)) S hS
  refine ⟨U ∪ T, hU.union hT, ?_⟩
  intro c hc hcycle
  have hcP : (P.complex.d (n + 1) n).hom ((e.hom.f (n + 1)).hom c) = 0 := by
    have hc' := congrArg (fun f => f.hom c) (e.hom.comm (n + 1) n)
    change (P.complex.d (n + 1) n).hom ((e.hom.f (n + 1)).hom c) =
      (e.hom.f n).hom (((Rep.standardComplex ℤ G).d (n + 1) n).hom c) at hc'
    rw [standardComplex_boundary_apply, hcycle] at hc'
    exact hc'.trans (map_zero (e.hom.f n).hom)
  obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp (P.exact_succ n) _ hcP
  refine ⟨(h.hom (n + 1) (n + 2)).hom c + (e.inv.f (n + 2)).hom b, ?_, ?_⟩
  · exact Submodule.add_mem _
      (controlledChainSpan_mono Set.subset_union_left (hh c hc))
      (controlledChainSpan_mono Set.subset_union_right (hα b))
  · have hδ := congrArg (fun f => f.hom b) (e.inv.comm (n + 2) (n + 1))
    change ((Rep.standardComplex ℤ G).d (n + 2) (n + 1)).hom
        ((e.inv.f (n + 2)).hom b) =
      (e.inv.f (n + 1)).hom ((P.complex.d (n + 2) (n + 1)).hom b) at hδ
    rw [hb] at hδ
    have hδ' := (standardComplex_boundary_apply ((e.inv.f (n + 2)).hom b)).symm.trans hδ
    have hm := h.comm (n + 1)
    rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at hm
    have hm' := congrArg (fun f => f.hom c) hm
    change c = (h.hom n (n + 1)).hom
        ((Q.complex.d (n + 1) n).hom c) +
      (Q.complex.d (n + 2) (n + 1)).hom
        ((h.hom (n + 1) (n + 2)).hom c) +
      (e.inv.f (n + 1)).hom ((e.hom.f (n + 1)).hom c) at hm'
    have hz : (Q.complex.d (n + 1) n).hom c = 0 := by
      change ((Rep.standardComplex ℤ G).d (n + 1) n).hom c = 0
      rw [standardComplex_boundary_apply, hcycle]
      rfl
    have hbd : (Q.complex.d (n + 2) (n + 1)).hom
        ((h.hom (n + 1) (n + 2)).hom c) =
        (tupleChainComplex ℤ G).d (n + 2) (n + 1)
          ((h.hom (n + 1) (n + 2)).hom c) :=
      standardComplex_boundary_apply _
    rw [hz, map_zero, zero_add, hbd] at hm'
    let z : MonoidAlgebra ℤ (Fin (n + 3) → G) := (h.hom (n + 1) (n + 2)).hom c
    let w : MonoidAlgebra ℤ (Fin (n + 3) → G) := (e.inv.f (n + 2)).hom b
    let D : MonoidAlgebra ℤ (Fin (n + 3) → G) →ₗ[ℤ]
        MonoidAlgebra ℤ (Fin (n + 2) → G) :=
      ((tupleChainComplex ℤ G).d (n + 2) (n + 1)).hom
    change D (z + w) = c
    rw [D.map_add]
    exact (congrArg (fun t => D z + t)
      hδ').trans hm'.symm

theorem TypeFP.controlledCycleFillings (h : TypeFP G (n + 2)) :
    HasControlledCycleFillings ℤ G n := by
  obtain ⟨P, hP⟩ := h
  exact controlledCycleFillings_of_resolution P (hP (n + 2) le_rfl)

end PolycyclicRecognition

end

end OAI
