import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPairwiseSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurviving

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
variable {I : Type*} [Fintype I] [DecidableEq I]

def longCoordinateMask (masks : I→ℕ→ℂ) (p : I→ℕ) (L S : I) (q : ℕ) : ℂ :=
  masks L q * ∏i∈frozenVertices L S,masks i (p i)

def shortCoordinateMask (masks : I→ℕ→ℂ) (S : I) (r : ℕ) : ℂ := masks S r

theorem coordinateMaskProduct_twoPrimeAssignment (masks : I→ℕ→ℂ) (p : I→ℕ)
    (L S : I) (hLS : L≠S) (q r : ℕ) :
    (∏i,masks i (twoPrimeAssignment p L S q r i)) =
      longCoordinateMask masks p L S q * shortCoordinateMask masks S r := by
  rw [prod_split_two L S hLS]
  simp only [twoPrimeAssignment_long p L S hLS q r,twoPrimeAssignment_short]
  have hf : (∏i∈frozenVertices L S,masks i (twoPrimeAssignment p L S q r i)) =
      ∏i∈frozenVertices L S,masks i (p i) :=
    Finset.prod_congr rfl (fun i hi=>congrArg (masks i) (twoPrimeAssignment_frozen p L S q r i hi))
  rw [hf]
  simp only [longCoordinateMask,shortCoordinateMask]
  ring

theorem norm_longCoordinateMask_le (masks : I→ℕ→ℂ) (hm : ∀i q,‖masks i q‖≤1)
    (p : I→ℕ) (L S : I) (q : ℕ) : ‖longCoordinateMask masks p L S q‖≤1 := by
  rw [longCoordinateMask,norm_mul,norm_prod]
  have hf : (∏i∈frozenVertices L S,‖masks i (p i)‖)≤1 :=
    Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hm i (p i))
  exact (mul_le_mul (hm L q) hf (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)

omit [Fintype I] [DecidableEq I] in
theorem norm_shortCoordinateMask_le (masks : I→ℕ→ℂ) (hm : ∀i q,‖masks i q‖≤1)
    (S : I) (r : ℕ) : ‖shortCoordinateMask masks S r‖≤1 := hm S r

def coordinateMembershipMask {A : ℕ} (E : I→Finset (Preliminaries.PrimeUpTo A))
    (e : I→I) (i : I) (q : ℕ) : ℂ :=
  if ∃p∈E (e i),p.val=q then 1 else 0

omit [Fintype I] [DecidableEq I] in
@[simp] theorem norm_coordinateMembershipMask_le {A : ℕ}
    (E : I→Finset (Preliminaries.PrimeUpTo A)) (e : I→I) (i : I) (q : ℕ) :
    ‖coordinateMembershipMask E e i q‖≤1 := by
  unfold coordinateMembershipMask
  split_ifs <;> norm_num

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
