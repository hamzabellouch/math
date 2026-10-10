import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneCharacter

namespace OAI

/-! # Supports of rank-one vectors in an induced representation

For induction from a normal subgroup, the quotient acts transitively on the
coordinate positions. A rank-one subrepresentation must therefore have either
empty support or every quotient coordinate in its support.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

section Coordinates
variable (k : Type) [CommRing k] (N : Subgroup G) [N.Normal] (A : Rep k N)

theorem inductionCoordinates_action_apply (g : G) (x : Rep.ind N.subtype A)
    (c : G ⧸ N) :
    inductionCoordinates k N A ((Rep.ind N.subtype A).ρ g x)
        (c * (QuotientGroup.mk' N g)⁻¹) =
      A.ρ (normalQuotientPart N (normalQuotientRepresentative N c * g⁻¹))⁻¹
        (inductionCoordinates k N A x c) := by
  classical
  let e := normalInductionEquiv k N A
  have h : (Finsupp.lapply (c * (QuotientGroup.mk' N g)⁻¹)).comp
      ((inductionCoordinates k N A).comp
        (((Rep.ind N.subtype A).ρ g).comp e.symm.toLinearMap)) =
      (A.ρ (normalQuotientPart N (normalQuotientRepresentative N c * g⁻¹))⁻¹).comp
        (Finsupp.lapply c) := by
    apply Finsupp.lhom_ext'
    intro b
    apply LinearMap.ext
    intro a
    change inductionCoordinates k N A
        ((Rep.ind N.subtype A).ρ g
          (inductionCoordinatesInv k N A (Finsupp.single b a)))
          (c * (QuotientGroup.mk' N g)⁻¹) =
      A.ρ (normalQuotientPart N (normalQuotientRepresentative N c * g⁻¹))⁻¹
        (Finsupp.single b a c)
    rw [inductionCoordinatesInv_single, ind_mk, inductionCoordinates_mk]
    simp only [(QuotientGroup.mk' N).map_mul, (QuotientGroup.mk' N).map_inv,
      normalQuotientRepresentative_mk]
    by_cases hbc : b = c
    · subst b
      simp
    · simp [hbc]
  have hx := LinearMap.congr_fun h (e x)
  change inductionCoordinates k N A ((Rep.ind N.subtype A).ρ g (e.symm (e x)))
      (c * (QuotientGroup.mk' N g)⁻¹) =
    A.ρ (normalQuotientPart N (normalQuotientRepresentative N c * g⁻¹))⁻¹ (e x c) at hx
  rw [LinearEquiv.symm_apply_apply] at hx
  exact hx

end Coordinates

attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

theorem rankOne_induced_hom_eq_zero (N : Subgroup G) [N.Normal] [Infinite (G ⧸ N)]
    (A : Rep ℤ N) (D : Rep ℤ G) (eD : D.V ≃ₗ[ℤ] ℤ)
    (f : D ⟶ Rep.ind N.subtype A) : f = 0 := by
  classical
  let v := eD.symm 1
  let y := f.hom v
  have hy : y = 0 := by
    apply (normalInductionEquiv ℤ N A).injective
    apply Finsupp.ext
    intro c
    by_contra hc
    have hc' : inductionCoordinates ℤ N A y c ≠ 0 := by
      change inductionCoordinates ℤ N A y c ≠ inductionCoordinates ℤ N A 0 c at hc
      simpa only [map_zero, Finsupp.zero_apply] using hc
    obtain ⟨d, hd⟩ := (inductionCoordinates ℤ N A y).support.exists_notMem
    have hd' : inductionCoordinates ℤ N A y d = 0 := Finsupp.notMem_support_iff.mp hd
    let g := normalQuotientRepresentative N (d⁻¹ * c)
    have hg : c * (QuotientGroup.mk' N g)⁻¹ = d := by
      change c * (QuotientGroup.mk' N (normalQuotientRepresentative N (d⁻¹ * c)))⁻¹ = d
      rw [normalQuotientRepresentative_mk, mul_inv_rev, inv_inv, ← mul_assoc,
        mul_inv_cancel, one_mul]
    let a := eD (D.ρ g v)
    have hv : D.ρ g v = a • v := by
      apply eD.injective
      rw [map_zsmul]
      simp [v, a]
    have hyact : (Rep.ind N.subtype A).ρ g y = a • y := by
      rw [show y = f.hom v from rfl, ← Rep.hom_comm_apply, hv, map_zsmul]
    have he := inductionCoordinates_action_apply ℤ N A g y c
    rw [hg, hyact, map_zsmul] at he
    change a • inductionCoordinates ℤ N A y d = _ at he
    rw [hd', zsmul_zero] at he
    have hi : Function.Injective (A.ρ
        (normalQuotientPart N (normalQuotientRepresentative N c * g⁻¹))⁻¹) :=
      by
        intro u v huv
        have h := congrArg (A.ρ (normalQuotientPart N (normalQuotientRepresentative N c * g⁻¹))) huv
        simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] using h
    exact hc' (hi (he.symm.trans (map_zero _).symm))
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  have hw : w = eD w • v := by
    apply eD.injective
    rw [map_zsmul]
    simp [v]
  change f.hom w = 0
  rw [hw, map_zsmul]
  exact (congrArg (fun z => eD w • z) hy).trans (zsmul_zero _)

end PolycyclicRecognition

end

end OAI
