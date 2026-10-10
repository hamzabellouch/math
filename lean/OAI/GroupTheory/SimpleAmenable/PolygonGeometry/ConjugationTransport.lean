import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.AlphabetAlignedGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConjugationTransport

variable {J M H T : Type*} [Group M] [Group H] [MulAction M T]

theorem word_conjugates_differences (p : J → M) (f : J → H) (Y : T → H)
    (R : T → T → Prop)
    (hR : ∀ (g : M) t u, R t u → R (g • t) (g • u))
    (hgen : ∀ j t u, R t u →
      f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (Y (p j • t))⁻¹ * Y (p j • u))
    (w : FreeGroup J) : ∀ t u, R t u →
      FreeGroup.lift f w * (Y t)⁻¹ * Y u * (FreeGroup.lift f w)⁻¹ =
        (Y (FreeGroup.lift p w • t))⁻¹ * Y (FreeGroup.lift p w • u) := by
  induction w using FreeGroup.induction_on with
  | one =>
      intro t u _
      simp
  | of j =>
      simpa only [FreeGroup.lift_apply_of] using hgen j
  | inv_of j ih =>
      intro t u htu
      have h := ih ((p j)⁻¹ • t) ((p j)⁻¹ • u) (hR _ _ _ htu)
      simp only [FreeGroup.lift_apply_of, smul_inv_smul] at h
      simp only [map_inv, FreeGroup.lift_apply_of]
      calc
        (f j)⁻¹ * (Y t)⁻¹ * Y u * ((f j)⁻¹)⁻¹ =
            (f j)⁻¹ * (f j * (Y ((p j)⁻¹ • t))⁻¹ *
                Y ((p j)⁻¹ • u) * (f j)⁻¹) * f j := by rw [h]; group
        _ = _ := by group
  | mul x y ihx ihy =>
      intro t u htu
      simp only [map_mul, mul_smul]
      calc
        (FreeGroup.lift f x * FreeGroup.lift f y) * (Y t)⁻¹ * Y u *
            (FreeGroup.lift f x * FreeGroup.lift f y)⁻¹ =
            FreeGroup.lift f x *
              (FreeGroup.lift f y * (Y t)⁻¹ * Y u * (FreeGroup.lift f y)⁻¹) *
              (FreeGroup.lift f x)⁻¹ := by group
        _ = FreeGroup.lift f x *
              ((Y (FreeGroup.lift p y • t))⁻¹ * Y (FreeGroup.lift p y • u)) *
              (FreeGroup.lift f x)⁻¹ := by rw [ihy t u htu]
        _ = _ := by
          simpa only [mul_assoc] using
            ihx _ _ (hR (FreeGroup.lift p y) t u htu)

theorem centralLaw_of_difference_conjugations
    (p : J → M) (f : J → H) (Y : T → H) (R : T → T → Prop)
    (hR : ∀ (g : M) t u, R t u → R (g • t) (g • u))
    (hgen : ∀ j t u, R t u →
      f j * (Y t)⁻¹ * Y u * (f j)⁻¹ =
        (Y (p j • t))⁻¹ * Y (p j • u))
    (hgenerate : Subgroup.closure {h : H | ∃ t u, R t u ∧ h = (Y t)⁻¹ * Y u} = ⊤) :
    HasCentralLaw (FreeGroup.lift p) (FreeGroup.lift f) := by
  rw [hasCentralLaw_iff]
  intro w hw
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← hgenerate,
    Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨t,u,htu,rfl⟩
  have h := word_conjugates_differences p f Y R hR hgen w t u htu
  rw [hw, one_smul, one_smul] at h
  have h' := congrArg (fun x => x * FreeGroup.lift f w) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'.symm

end ConjugationTransport

end SimpleAmenable
end
end

end OAI
