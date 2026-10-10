import Mathlib
import OAI.Geometry.Cannon.Conformal.SphereTile

namespace OAI

section
noncomputable section
namespace CannonMobius
open Set
open scoped OnePoint

lemma analytic_fix_infty_eq_affine (f : Sphere ≃ₜ Sphere) (hInfinity : f ∞=∞)
    (hf : f ∈ biholomorphic) : ∃ a b : ℂ, ∃ ha : a ≠ 0, f=affine a b ha := by
  obtain ⟨a,b,ha,he⟩ := analytic_fix_infty_affine f hInfinity hf.1 hf.2
  refine ⟨a,b,ha,?_⟩
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => exact hInfinity
  | coe z => exact he z

theorem biholomorphic_normal_form (f : Sphere ≃ₜ Sphere) (hf : f ∈ biholomorphic) :
    (∃ a b : ℂ, ∃ ha : a ≠ 0, f=affine a b ha) ∨
    (∃ p a b : ℂ, ∃ ha : a ≠ 0,
      f=affine 1 p one_ne_zero*inversion*affine a b ha) := by
  by_cases hInfinity : f ∞=∞
  · exact Or.inl (analytic_fix_infty_eq_affine f hInfinity hf)
  · have hp : ∃ p : ℂ, f ∞=(p:Sphere) := by
      induction h : f ∞ using OnePoint.rec with
      | infty => exact (hInfinity h).elim
      | coe p => exact ⟨p,rfl⟩
    obtain ⟨p,hp⟩ := hp
    let N : Sphere ≃ₜ Sphere := inversion*affine 1 (-p) one_ne_zero
    have hNg : N ∈ biholomorphic := biholomorphic.mul_mem inversion_biholomorphic
      (affine_biholomorphic 1 (-p) one_ne_zero)
    have hNf : (N*f) ∞=∞ := by
      change inv (affine 1 (-p) one_ne_zero (f ∞))=∞
      rw [hp,affine_coe]
      simp only [one_mul,add_neg_cancel,inv_zero]
    obtain ⟨a,b,ha,he⟩ := analytic_fix_infty_eq_affine (N*f) hNf (biholomorphic.mul_mem hNg hf)
    have hNi : N⁻¹=affine 1 p one_ne_zero*inversion := by
      rw [show N=inversion*affine 1 (-p) one_ne_zero from rfl,mul_inv_rev]
      change (affine 1 (-p) one_ne_zero).symm*inversion=affine 1 p one_ne_zero*inversion
      rw [affine_symm]
      simp only [inv_one,neg_neg,div_one]
    refine Or.inr ⟨p,a,b,ha,?_⟩
    calc
      f=N⁻¹*(N*f) := by rw [← mul_assoc,inv_mul_cancel,one_mul]
      _=affine 1 p one_ne_zero*inversion*affine a b ha := by rw [hNi,he]

theorem biholomorphic_mem_of_generators (S : Subgroup (Sphere ≃ₜ Sphere))
    (ha : ∀ a b : ℂ, ∀ h : a ≠ 0, affine a b h ∈ S) (hi : inversion ∈ S)
    {f : Sphere ≃ₜ Sphere} (hf : f ∈ biholomorphic) : f ∈ S := by
  rcases biholomorphic_normal_form f hf with ⟨a,b,h,rfl⟩ | ⟨p,a,b,h,rfl⟩
  · exact ha a b h
  · exact S.mul_mem (S.mul_mem (ha 1 p one_ne_zero) hi) (ha a b h)
end CannonMobius

end
end

end OAI
