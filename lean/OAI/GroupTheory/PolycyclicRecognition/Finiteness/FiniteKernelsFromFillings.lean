import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledFillingsFromResolution
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralRepresentationMap

namespace OAI

/-! # Controlled fillings make the next resolution kernel finite

The kernel is the sum of two finite images: controlled fillers mapped back
from homogeneous chains, and the comparison homotopy applied to the finite
resolution term. This proves finite generation without assuming noetherianity
of the group ring.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] {n : ℕ}

theorem resolution_comp_range_le_kernel
    (P : ProjectiveResolution (trivialIntegral G)) {A : Rep.{0} ℤ G}
    (f : A ⟶ P.complex.X (n + 2)) :
    LinearMap.range (integralRepresentationMap (f ≫ P.complex.d (n + 2) (n + 1))) ≤
      LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n)) := by
  rintro _ ⟨a, rfl⟩
  change integralRepresentationMap (f ≫ P.complex.d (n + 2) (n + 1) ≫
    P.complex.d (n + 1) n) a = 0
  rw [P.complex.d_comp_d, comp_zero, integralRepresentationMap_zero]
  rfl

theorem finite_resolution_kernel_of_controlledFillings
    (P : ProjectiveResolution (trivialIntegral G))
    (hfin : IntegralRepresentationFinite G (P.complex.X (n + 1)))
    (hfill : HasControlledCycleFillings ℤ G n) :
    (LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n))).FG := by
  let Q := Rep.standardResolution ℤ G
  let e := ProjectiveResolution.homotopyEquiv P Q
  let h := e.homotopyHomInvId.symm
  obtain ⟨S, hS, hα⟩ := finiteRepresentation_range_controlled
    (P.complex.X (n + 1)) hfin (e.hom.f (n + 1))
  obtain ⟨T, hT, hTfill⟩ := hfill S hS
  let F := integralRepresentationMap
    (e.inv.f (n + 2) ≫ P.complex.d (n + 2) (n + 1))
  let H := integralRepresentationMap
    (h.hom (n + 1) (n + 2) ≫ P.complex.d (n + 2) (n + 1))
  let C := (controlledChainSubrepresentation (R := ℤ) (n := n + 2) T).asSubmodule
  let N := C.map F ⊔ LinearMap.range H
  have hN : N.FG := by
    apply Submodule.FG.sup
    · exact (controlledChainSubrepresentation_fg T hT).map F
    · have : Module.Finite ℤ[G] (P.complex.X (n + 1)).ρ.asModule := hfin
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := ℤ[G]) (M := (P.complex.X (n + 1)).ρ.asModule)).map H
  have hNK : N ≤ LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n)) := by
    apply sup_le
    · exact (Submodule.map_mono le_top).trans
        (by simpa only [Submodule.map_top] using
          resolution_comp_range_le_kernel P (e.inv.f (n + 2)))
    · exact resolution_comp_range_le_kernel P (h.hom (n + 1) (n + 2))
  have hKN : LinearMap.ker (integralRepresentationMap (P.complex.d (n + 1) n)) ≤ N := by
    intro z hz
    have hz' : (P.complex.d (n + 1) n).hom z = 0 := hz
    have hcycle : (tupleChainComplex ℤ G).d (n + 1) n ((e.hom.f (n + 1)).hom z) = 0 := by
      have hc := congrArg (fun f => f.hom z) (e.hom.comm (n + 1) n)
      change (Q.complex.d (n + 1) n).hom ((e.hom.f (n + 1)).hom z) =
        (e.hom.f n).hom ((P.complex.d (n + 1) n).hom z) at hc
      rw [hz', map_zero] at hc
      exact (standardComplex_boundary_apply _).symm.trans hc
    obtain ⟨b, hb, hdb⟩ := hTfill _ (hα z) hcycle
    have hm := h.comm (n + 1)
    rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at hm
    have hm' := congrArg (fun f => f.hom z) hm
    change z = (h.hom n (n + 1)).hom ((P.complex.d (n + 1) n).hom z) +
      (P.complex.d (n + 2) (n + 1)).hom ((h.hom (n + 1) (n + 2)).hom z) +
      (e.inv.f (n + 1)).hom ((e.hom.f (n + 1)).hom z) at hm'
    rw [hz', map_zero, zero_add] at hm'
    have hmap := congrArg (fun f => f.hom b) (e.inv.comm (n + 2) (n + 1))
    change (P.complex.d (n + 2) (n + 1)).hom ((e.inv.f (n + 2)).hom b) =
      (e.inv.f (n + 1)).hom ((Q.complex.d (n + 2) (n + 1)).hom b) at hmap
    have hdb' : (Q.complex.d (n + 2) (n + 1)).hom b = (e.hom.f (n + 1)).hom z :=
      (standardComplex_boundary_apply b).trans hdb
    rw [hdb'] at hmap
    apply Submodule.mem_sup.mpr
    refine ⟨F b, ?_, H z, ⟨z, rfl⟩, ?_⟩
    · exact ⟨b, hb, rfl⟩
    · change (P.complex.d (n + 2) (n + 1)).hom ((e.inv.f (n + 2)).hom b) +
        (P.complex.d (n + 2) (n + 1)).hom ((h.hom (n + 1) (n + 2)).hom z) = z
      rw [hmap]
      exact (add_comm _ _).trans hm'.symm
  rw [le_antisymm hKN hNK]
  exact hN

end PolycyclicRecognition

end

end OAI
