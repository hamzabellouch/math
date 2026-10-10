import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceRoleBounds
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries HigherBiasSourceWord HigherBiasSourceRoleBounds
open scoped BigOperators

def sourceHalfMask {Q m nc : ℕ} (J : ℤ)
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) : ℝ := binIndicator J (originalWord w)

lemma sourceHalfMask_bounds {Q m nc : ℕ} (J : ℤ)
    (w : Fin ((m+1)+nc) → PrimeUpTo Q) :
    0 ≤ sourceHalfMask J w ∧ sourceHalfMask J w ≤ 1 := by
  unfold sourceHalfMask binIndicator
  split_ifs <;> norm_num

lemma sourceHalf_subsets {Q m nc : ℕ} (E bulk top : Finset (PrimeUpTo Q))
    (cells : Fin nc → Finset (PrimeUpTo Q)) (hb : bulk⊆E) (ht : top⊆E)
    (hc : ∀ i,cells i⊆E) : ∀ i,halfRoleShells bulk top m cells i⊆E := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro l
      simpa only [halfRoleShells,roleShells,Fin.append_left] using hb
    · intro l
      simpa only [halfRoleShells,roleShells,Fin.append_left,Fin.append_right] using ht
  · intro j
    simpa only [halfRoleShells,Fin.append_right] using hc j

theorem sourceHalfMean_lower {d : Decomposition} {Q m nc : ℕ}
    {E : Finset (PrimeUpTo Q)} {δ : ℝ} (F : HigherBiasSourceFamily d Q E δ)
    (bulk top : Finset (PrimeUpTo Q)) (cells : Fin nc → Finset (PrimeUpTo Q))
    (hb : 0 < primeShellMass bulk) (ht : 0 < primeShellMass top)
    (hc : ∀ i,0 < primeShellMass (cells i)) (J n : ℤ) {g e : ℝ}
    (hg : 0 ≤ g) (he : 0 ≤ e)
    (hword : g ≤ ‖initialCharacterMean (roleShells bulk top m)
      (roleShells_mass_pos hb ht m) (fun _=>familyCharacter F)
      (fun _=>familyCenter F) (fun _=>familyPhase F) (binIndicator J) n‖)
    (hcell : ∀ i,e ≤ ((primeShellPrior (cells i) (hc i)).cmean
      (fun p=>F.test p (n:ZMod p.val))).re) :
    g*e^nc ≤ ‖initialCharacterMean (halfRoleShells bulk top m cells)
      (halfRole_mass_pos bulk top m cells hb ht hc)
      (fun _=>familyCharacter F) (fun _=>familyCenter F) (fun _=>familyPhase F)
      (sourceHalfMask J) n‖ := by
  rw [show sourceHalfMask (Q:=Q) (m:=m) (nc:=nc) J =
    (fun w=>binIndicator J (fun i=>w (Fin.castAdd nc i))) from rfl]
  rw [initialCharacterMean_split]
  simp only [halfRoleShells,Fin.append_left,Fin.append_right,family_phasedCharacter]
  exact initial_word_cells_norm_lower _ _ hg he hword hcell

end Ostmann.Characters.HigherBiasSource

end

end OAI
