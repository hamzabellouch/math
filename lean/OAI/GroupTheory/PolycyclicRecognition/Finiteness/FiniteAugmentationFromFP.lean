import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ChosenIntegralResolution
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralRepresentationMap
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicFiniteness

namespace OAI

/-! # FP one gives a finitely generated augmentation kernel

A resolution comparison expresses the kernel as a sum of two finite images.
The argument does not assume that the group is finitely generated.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem TypeFP.augmentationKernel_fg (hG : TypeFP G 1) :
    (LinearMap.ker (integralRepresentationMap
      (Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1))).FG := by
  obtain ⟨P, hP⟩ := hG
  let Q := chosenIntegralResolution G
  let e := ProjectiveResolution.homotopyEquiv Q P
  let h := e.homotopyHomInvId.symm
  let F := integralRepresentationMap (e.inv.f 1 ≫ Q.complex.d 1 0)
  let H := integralRepresentationMap (h.hom 0 1 ≫ Q.complex.d 1 0)
  let N := LinearMap.range F ⊔ LinearMap.range H
  have hN : N.FG := by
    apply Submodule.FG.sup
    · have : Module.Finite ℤ[G] (P.complex.X 1).ρ.asModule := hP 1 le_rfl
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := ℤ[G]) (M := (P.complex.X 1).ρ.asModule)).map F
    · have : Module.Finite ℤ[G] (Q.complex.X 0).ρ.asModule :=
        integralRepresentationFinite_leftRegular G
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := ℤ[G]) (M := (Q.complex.X 0).ρ.asModule)).map H
  have hπ : Q.π.f 0 = Rep.leftRegularHom (Rep.trivial ℤ G ℤ) 1 := rfl
  change (LinearMap.ker (integralRepresentationMap (Q.π.f 0))).FG
  have hNK : N ≤ LinearMap.ker (integralRepresentationMap (Q.π.f 0)) := by
    apply sup_le <;> rintro _ ⟨a, rfl⟩
    · change integralRepresentationMap (e.inv.f 1 ≫ Q.complex.d 1 0 ≫ Q.π.f 0) a = 0
      rw [Q.complex_d_comp_π_f_zero, comp_zero, integralRepresentationMap_zero]
      rfl
    · change integralRepresentationMap (h.hom 0 1 ≫ Q.complex.d 1 0 ≫ Q.π.f 0) a = 0
      rw [Q.complex_d_comp_π_f_zero, comp_zero, integralRepresentationMap_zero]
      rfl
  have hKN : LinearMap.ker (integralRepresentationMap (Q.π.f 0)) ≤ N := by
    intro z hz
    let z0 : Q.complex.X 0 := (Q.complex.X 0).ρ.asModuleEquiv z
    have hz' : (Q.π.f 0).hom z0 = 0 := hz
    have hcycle : (P.π.f 0).hom ((e.hom.f 0).hom z0) = 0 := by
      have hc := congrArg (fun f => f.hom z0)
        (ProjectiveResolution.lift_commutes_zero (𝟙 (trivialIntegral G)) Q P)
      change (P.π.f 0).hom ((e.hom.f 0).hom z0) = (Q.π.f 0).hom z0 at hc
      exact hc.trans hz'
    obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp P.exact₀ _ hcycle
    have hm := h.comm 0
    rw [Homotopy.dNext_zero_chainComplex, prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel 1 0)] at hm
    have hm' := congrArg (fun f => f.hom z0) hm
    change z0 = 0 + (Q.complex.d 1 0).hom ((h.hom 0 1).hom z0) +
      (e.inv.f 0).hom ((e.hom.f 0).hom z0) at hm'
    rw [zero_add] at hm'
    have hmap := congrArg (fun f => f.hom b) (e.inv.comm 1 0)
    change (Q.complex.d 1 0).hom ((e.inv.f 1).hom b) =
      (e.inv.f 0).hom ((P.complex.d 1 0).hom b) at hmap
    rw [hb] at hmap
    apply Submodule.mem_sup.mpr
    refine ⟨F b, ⟨b, rfl⟩, H z, ⟨z, rfl⟩, ?_⟩
    change (Q.complex.d 1 0).hom ((e.inv.f 1).hom b) +
      (Q.complex.d 1 0).hom ((h.hom 0 1).hom z0) = z0
    rw [hmap]
    exact (add_comm _ _).trans hm'.symm
  rw [le_antisymm hKN hNK]
  exact hN

end PolycyclicRecognition

end

end OAI
