import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingBaseCoordinates
import Mathlib.GroupTheory.Abelianization.Defs

namespace OAI

/-! # Transport of finite ascending bases along equivariant homomorphisms -/

noncomputable section
namespace PolycyclicRecognition
variable {G Q : Type} [Group G] [Group Q]

def HasFinitelyGeneratedAscendingBase (α : MulAut G) : Prop :=
  ∃ B : Subgroup G, B.FG ∧ B.map α.toMonoidHom ≤ B ∧
    ∀ g, ∃ n, g ∈ automorphismStage α B n

theorem automorphism_pow_equivariant (q : G →* Q) (α : MulAut G) (β : MulAut Q)
    (h : ∀ g, q (α g) = β (q g)) (n : ℕ) (g : G) :
    q ((α ^ n) g) = (β ^ n) (q g) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', MulAut.mul_apply, h, ih]

theorem HasFinitelyGeneratedAscendingBase.of_surjective
    (q : G →* Q) (hq : Function.Surjective q) (α : MulAut G) (β : MulAut Q)
    (h : ∀ g, q (α g) = β (q g)) (hα : HasFinitelyGeneratedAscendingBase α) :
    HasFinitelyGeneratedAscendingBase β := by
  obtain ⟨B, hBfg, hBstable, hBcover⟩ := hα
  refine ⟨B.map q, fg_subgroup_map hBfg q, ?_, ?_⟩
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨α g, hBstable ⟨g, hg, rfl⟩, h g⟩
  · intro x
    obtain ⟨g, rfl⟩ := hq x
    obtain ⟨n, hn⟩ := hBcover g
    refine ⟨n, (mem_automorphismStage_iff _ _ _ _).mpr ?_⟩
    exact ⟨(α ^ n) g, (mem_automorphismStage_iff _ _ _ _).mp hn,
      automorphism_pow_equivariant q α β h n g⟩

theorem HasFinitelyGeneratedAscendingBase.of_equiv
    (e : G ≃* Q) (α : MulAut G) (β : MulAut Q)
    (h : ∀ g, e (α g) = β (e g)) (hβ : HasFinitelyGeneratedAscendingBase β) :
    HasFinitelyGeneratedAscendingBase α := by
  apply hβ.of_surjective e.symm.toMonoidHom e.symm.surjective β α
  intro x
  apply e.injective
  change e (e.symm (β x)) = e (α (e.symm x))
  rw [e.apply_symm_apply, h, e.apply_symm_apply]

theorem abelianization_map_surjective (q : G →* Q) (hq : Function.Surjective q) :
    Function.Surjective (Abelianization.map q) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
  obtain ⟨g, rfl⟩ := hq y
  exact ⟨Abelianization.of g, rfl⟩

theorem ascendingBase_abelianization_of_surjective
    (q : G →* Q) (hq : Function.Surjective q) (α : MulAut G) (β : MulAut Q)
    (h : ∀ g, q (α g) = β (q g))
    (hα : HasFinitelyGeneratedAscendingBase (characteristicQuotientAut (commutator G) α)) :
    HasFinitelyGeneratedAscendingBase (characteristicQuotientAut (commutator Q) β) := by
  apply hα.of_surjective (Abelianization.map q) (abelianization_map_surjective q hq)
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) x
  change Abelianization.of (q (α g)) = Abelianization.of (β (q g))
  rw [h]

end PolycyclicRecognition

end

end OAI
