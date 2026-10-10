import OAI.GroupTheory.PolycyclicRecognition.Algebra.AutomorphismExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CharacteristicQuotientAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift

namespace OAI

/-! # Coordinates for lifting a stable ascending base -/

noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type} [Group G] [Group Q]

theorem exists_fg_subgroup_map_eq (q : G →* Q) (hq : Function.Surjective q)
    (P : Subgroup Q) (hP : P.FG) : ∃ H : Subgroup G, H.FG ∧ H.map q = P := by
  obtain ⟨S, hS, hfin⟩ := (Subgroup.fg_iff P).mp hP
  choose s hs using hq
  refine ⟨Subgroup.closure (s '' S), (Subgroup.fg_iff _).mpr
    ⟨s '' S, rfl, hfin.image s⟩, ?_⟩
  rw [MonoidHom.map_closure]
  have he : q '' (s '' S) = S := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [hs] using hy
    · intro hx
      exact ⟨s x, ⟨x, hx, rfl⟩, hs x⟩
  rw [he, hS]

theorem characteristic_pow_apply (N : Subgroup G) [N.Characteristic]
    (α : MulAut G) (n : ℕ) (g : N) :
    (((MulAut.characteristic N α) ^ n) g : G) = (α ^ n) (g : G) := by
  rw [← map_pow]
  rfl

theorem characteristicQuotient_pow_mk (N : Subgroup G) [N.Characteristic]
    (α : MulAut G) (n : ℕ) (g : G) :
    (characteristicQuotientAut N α ^ n) ((QuotientGroup.mk' N) g) =
      (QuotientGroup.mk' N) ((α ^ n) g) := by
  rw [← map_pow]
  rfl

end PolycyclicRecognition

end

end OAI
