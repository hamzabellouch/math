import Mathlib
import OAI.Computability.MaxCut.Estimates.Param

namespace OAI

noncomputable section
namespace OptimalMaxCut.Unweighted
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {p : ℕ} [Fact p.Prime]
 theorem vecEquiv_symm_val (x : Fin (p^6)) (k : Fin 6) :
    ((vecEquiv (p := p)).symm x k).val = x.val / p^k.val % p := by
  change ((ZMod.finEquiv p) ((finFunctionFinEquiv (m := p) (n := 6)).symm x k)).val = _
  cases p with
  | zero => exact False.elim (Nat.not_prime_zero Fact.out)
  | succ p => rfl
 theorem vertexEquiv_symm_first {N : ℕ} (i : Fin (N*p^6)) :
    ((vertexEquiv N).symm i).1.val = i.val / p^6 := rfl
 theorem vertexEquiv_symm_second {N : ℕ} (i : Fin (N*p^6)) (k : Fin 6) :
    (((vertexEquiv N).symm i).2 k).val = RawGrid.coordinate p i.val k.val := by
  exact vecEquiv_symm_val _ _
 theorem dot_val (x y : Vec p) : (dot x y).val = (∑ k : Fin 6, (x k).val*(y k).val)%p := by
  have he : dot x y = ((∑ k : Fin 6, (x k).val*(y k).val : ℕ) : ZMod p) := by
    simp only [Nat.cast_sum,Nat.cast_mul,ZMod.natCast_zmod_val,dot]
  rw [he, ZMod.val_natCast]
 theorem residue_membership (a : ZMod p) (w : ℚ) :
    a ∈ residueSet w ↔ ∃ r < ⌊(p:ℚ)*w⌋₊, r%p=a.val := by
  simp only [residueSet,mem_image,mem_range]
  constructor
  · rintro ⟨r,hr,he⟩
    exact ⟨r,hr,by simpa only [ZMod.val_natCast] using congrArg ZMod.val he⟩
  · rintro ⟨r,hr,he⟩
    exact ⟨r,hr,ZMod.val_injective p (by simpa only [ZMod.val_natCast] using he)⟩
end OptimalMaxCut.Unweighted

end

end OAI
