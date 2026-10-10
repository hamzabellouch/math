import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinMasks

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

theorem coordinateMembershipMask_prime {A : ℕ} (E : I→Finset (PrimeUpTo A))
    (e : I→I) (i : I) (q : PrimeUpTo A) :
    coordinateMembershipMask E e i q.val = if q∈E (e i) then 1 else 0 := by
  have he : (∃p∈E (e i),p.val=q.val) ↔ q∈E (e i) := by
    constructor
    · rintro ⟨p,hp,hpq⟩
      exact (Subtype.val_injective hpq) ▸ hp
    · intro hq
      exact ⟨q,hq,rfl⟩
  simp only [coordinateMembershipMask,he]

def pairedCoordinateMembershipMask {A : ℕ} (E : I→Finset (PrimeUpTo A))
    (σ ρ : Equiv.Perm I) (i : I) (q : ℕ) : ℂ :=
  coordinateMembershipMask E σ i q * coordinateMembershipMask E ρ i q

omit [Fintype I] [DecidableEq I] in
theorem pairedCoordinateMembershipMask_norm {A : ℕ} (E : I→Finset (PrimeUpTo A))
    (σ ρ : Equiv.Perm I) (i : I) (q : ℕ) :
    ‖pairedCoordinateMembershipMask E σ ρ i q‖≤1 := by
  rw [pairedCoordinateMembershipMask,norm_mul]
  exact (mul_le_mul (norm_coordinateMembershipMask_le E σ i q)
    (norm_coordinateMembershipMask_le E ρ i q) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [DecidableEq I] in

theorem pairedCoordinateMembershipMask_product {A : ℕ}
    (E : I→Finset (PrimeUpTo A)) (σ ρ : Equiv.Perm I) (x : I→PrimeUpTo A) :
    (∏i,pairedCoordinateMembershipMask E σ ρ i (x i).val) =
      if (∀i,x (σ.symm i)∈E i) ∧ (∀i,x (ρ.symm i)∈E i) then 1 else 0 := by
  have hs : (∀i,x (σ.symm i)∈E i) ↔ ∀i,x i∈E (σ i) := by
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (σ i)
    · intro h i
      simpa only [Equiv.apply_symm_apply] using h (σ.symm i)
  have hr : (∀i,x (ρ.symm i)∈E i) ↔ ∀i,x i∈E (ρ i) := by
    constructor
    · intro h i
      simpa only [Equiv.symm_apply_apply] using h (ρ i)
    · intro h i
      simpa only [Equiv.apply_symm_apply] using h (ρ.symm i)
  simp only [hs,hr]
  by_cases h : (∀i,x i∈E (σ i)) ∧ (∀i,x i∈E (ρ i))
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    simp only [pairedCoordinateMembershipMask,coordinateMembershipMask_prime,
      ite_eq_left (h.1 i),ite_eq_left (h.2 i),one_mul]
  · rw [ite_eq_right h]
    have he : ∃i,¬(x i∈E (σ i) ∧ x i∈E (ρ i)) := by
      by_contra hn
      push Not at hn
      exact h ⟨fun i=>(hn i).1,fun i=>(hn i).2⟩
    obtain ⟨i,hi⟩ := he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : x i∈E (σ i)
    · have hr : x i∉E (ρ i) := fun hr=>hi ⟨hs,hr⟩
      simp only [pairedCoordinateMembershipMask,coordinateMembershipMask_prime,
        ite_eq_right hr,mul_zero]
    · simp only [pairedCoordinateMembershipMask,coordinateMembershipMask_prime,
        ite_eq_right hs,zero_mul]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
