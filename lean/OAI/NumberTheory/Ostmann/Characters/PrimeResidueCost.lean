import OAI.NumberTheory.Ostmann.Characters.PrimeFrequencyExposure

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Preliminaries

def shellResidueCost {N:ℕ} {J:Type*} [Fintype J]
    (E:Finset (PrimeUpTo N)) (hE:0<primeShellMass E) : NNReal :=
  ⟨3*Fintype.card J/primeShellMass E,by positivity⟩

theorem primeResidueCost_le_shell {N Q:ℕ} [NeZero Q] {J:Type*} [Fintype J]
    (E:Finset (PrimeUpTo N)) (hE:0<primeShellMass E) :
    primeResidueCost (Q:=Q) (J:=J) E hE ≤ shellResidueCost (J:=J) E hE := by
  change 3*Fintype.card J*(Fintype.card (ZMod Q)ˣ:ℝ)/((Q:ℝ)*primeShellMass E) ≤
    3*Fintype.card J/primeShellMass E
  have hQ : (0:ℝ)<Q := by exact_mod_cast NeZero.pos Q
  have hc : (Fintype.card (ZMod Q)ˣ:ℝ)≤Q := by
    exact_mod_cast (ZMod.card_units_eq_totient Q ▸ Nat.totient_le Q)
  apply (div_le_iff₀ (mul_pos hQ hE)).mpr
  have he : (3*(Fintype.card J:ℝ)/primeShellMass E)*((Q:ℝ)*primeShellMass E)=
      3*(Fintype.card J:ℝ)*(Q:ℝ) := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hc (by positivity)

theorem binary_cost_mono (D E:List Bool→NNReal) (h:∀p,D p≤E p) (j:ℕ) (p:List Bool) :
    BinaryPriorExposure.cost D j p ≤ BinaryPriorExposure.cost E j p := by
  induction j generalizing p with
  | zero => exact h p
  | succ j ih => exact mul_le_mul' (ih _) (ih _)

end Ostmann.Characters

end

end OAI
