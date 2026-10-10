import Mathlib
import OAI.NumberTheory.Jacobsthal.Analysis.PairDensityExpansion

namespace OAI

namespace Erdos970

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.decEq

noncomputable def positionResidues (S : Finset ℕ) (p : ℕ) : Finset (ZMod p) := S.image (fun j : ℕ => (j : ZMod p))

noncomputable def forbiddenClasses (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) : Finset (ZMod p) :=
  S.image (fun j : ℕ => c-(u : ZMod p)*(j : ZMod p))

theorem affine_forbidden_injective (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) :
    Function.Injective (fun x : ZMod p => c-(u : ZMod p)*x) := by
  intro x y h
  have hm : (u : ZMod p)*x = (u : ZMod p)*y := by linear_combination -h
  have hh := congrArg (fun z : ZMod p => (↑(u⁻¹) : ZMod p)*z) hm
  simpa only [← mul_assoc,u.inv_mul,one_mul] using hh

theorem forbiddenClasses_card (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c : ZMod p) :
    (forbiddenClasses S p u c).card = (positionResidues S p).card := by
  have he : forbiddenClasses S p u c = (positionResidues S p).image (fun x => c-(u : ZMod p)*x) := by
    simp only [forbiddenClasses,positionResidues,Finset.image_image,Function.comp_def]
  rw [he,Finset.card_image_of_injective _ (affine_forbidden_injective p u c)]

theorem mem_forbiddenClasses (S : Finset ℕ) (p : ℕ) (u : (ZMod p)ˣ) (c x : ZMod p) :
    x ∈ forbiddenClasses S p u c ↔ ∃ j ∈ S,x+(u : ZMod p)*(j : ZMod p) = c := by
  simp only [forbiddenClasses,Finset.mem_image]
  constructor
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by linear_combination -he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨j,hj,by linear_combination -he⟩

theorem positionResidues_le_positions (S : Finset ℕ) (p : ℕ) : (positionResidues S p).card ≤ S.card :=
  Finset.card_image_le

theorem positionResidues_le_modulus (S : Finset ℕ) (p : ℕ) [NeZero p] : (positionResidues S p).card ≤ p := by
  have hh := Finset.card_le_univ (positionResidues S p)
  simpa only [ZMod.card] using hh

theorem forbiddenClasses_full_of_card (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) (hfull : (positionResidues S p).card = p) :
    forbiddenClasses S p u c = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp only [Finset.card_univ,ZMod.card,forbiddenClasses_card,hfull]
  exact le_rfl

end ErdosVarianceMoments

end

section

namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def positionDensity (S : Finset ℕ) (p : ℕ) : ℝ :=
  ((positionResidues S p).card : ℝ)/(p : ℝ)

noncomputable def jointDensity (P S : Finset ℕ) : ℝ := ∏ p ∈ P,(1-positionDensity S p)

theorem positionDensity_bounds (S : Finset ℕ) (p : ℕ) [NeZero p] :
    0 ≤ positionDensity S p ∧ positionDensity S p ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  refine ⟨by dsimp [positionDensity];positivity,?_⟩
  apply (div_le_one hp).mpr
  exact_mod_cast positionResidues_le_modulus S p

theorem positionDensity_le_two (S : Finset ℕ) (hS : S.card ≤ 2) (p : ℕ) [NeZero p] :
    positionDensity S p ≤ 2/(p : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (positionResidues_le_positions S p).trans hS

theorem positionResidues_singleton (j p : ℕ) : (positionResidues {j} p).card = 1 := by
  simp only [positionResidues,Finset.image_singleton,Finset.card_singleton]

theorem positionResidues_pair (i j p : ℕ) :
    (positionResidues {i,j} p).card = if Nat.ModEq p i j then 1 else 2 := by
  by_cases h : Nat.ModEq p i j
  · have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    simp only [positionResidues,Finset.image_insert,Finset.image_singleton,he,Finset.insert_eq_of_mem
      (Finset.mem_singleton_self _),Finset.card_singleton,ite_eq_left h]
  · have he : (i : ZMod p) ≠ (j : ZMod p) := by
      intro he
      exact h ((ZMod.natCast_eq_natCast_iff _ _ _).mp he)
    have hnot : (i : ZMod p) ∉ ({(j : ZMod p)} : Finset (ZMod p)) := by
      simpa only [Finset.mem_singleton] using he
    simp only [positionResidues,Finset.image_insert,Finset.image_singleton,
      Finset.card_insert_of_notMem hnot,Finset.card_singleton,ite_eq_right h]

theorem jointDensity_singleton (P : Finset ℕ) (j : ℕ) :
    jointDensity P {j} = ErdosRandomVariance.sieveProduct P := by
  simp only [jointDensity,positionDensity,positionResidues_singleton,Nat.cast_one,ErdosRandomVariance.sieveProduct]

theorem jointDensity_pair (P : Finset ℕ) (i j : ℕ) :
    jointDensity P {i,j} = ErdosRandomVariance.pairKernel P i j := by
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases h : Nat.ModEq p i j
  · simp only [positionDensity,positionResidues_pair,ite_eq_left h,Nat.cast_one,
      ErdosRandomVariance.congruenceIndicator]
    ring
  · simp only [positionDensity,positionResidues_pair,ite_eq_right h,Nat.cast_ofNat,
      ErdosRandomVariance.congruenceIndicator]
    ring

end ErdosVarianceMoments

end

end Erdos970

end OAI
