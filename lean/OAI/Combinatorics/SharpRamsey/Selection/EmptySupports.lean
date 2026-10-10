import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.OriginalFamilies

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_lower {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Nat.card K:ℝ)^d≤Fintype.card (Projectivization K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  push_cast
  exact single_le_sum (fun i hi=>pow_nonneg (Nat.cast_nonneg _) _) (mem_range.mpr (by omega))

def emptyOriginal {n : ℕ} {b : ℝ} (hdim : Module.finrank K V=n+3) (hb : 0≤b) :
    Original (K:=K) (V:=V) n b where
  A := univ
  B := univ
  nonemptyA := by
    have h:=projective_card_lower (show Module.finrank K V=(n+2)+1 by omega)
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
    have : 0<Fintype.card (Projectivization K V) := by exact_mod_cast (pow_pos hq (n+2)).trans_le h
    exact card_pos.mp (by simpa using this)
  nonemptyB := by
    have hdim' : Module.finrank K (Module.Dual K V)=(n+2)+1 := by rw [Subspace.dual_finrank_eq]; omega
    have h:=projective_card_lower hdim'
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.zero_lt_one.trans (Finite.one_lt_card (α:=K))
    have : 0<Fintype.card (Projectivization K (Module.Dual K V)) := by exact_mod_cast (pow_pos hq (n+2)).trans_le h
    exact card_pos.mp (by simpa using this)
  product := by
    have ha:=projective_card_lower (show Module.finrank K V=(n+2)+1 by omega)
    have hdim' : Module.finrank K (Module.Dual K V)=(n+2)+1 := by rw [Subspace.dual_finrank_eq]; omega
    have hb':=projective_card_lower hdim'
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    calc
      _ ≤ (Nat.card K:ℝ)^(n+3)*1 := mul_le_mul_of_nonneg_left
        (exp_le_one_iff.mpr (by linarith)) (pow_nonneg (by linarith) _)
      _ ≤ (Nat.card K:ℝ)^((n+2)+(n+2)) := by rw [mul_one]; exact pow_le_pow_right₀ hq (by omega)
      _ = (Nat.card K:ℝ)^(n+2)*(Nat.card K:ℝ)^(n+2) := pow_add ..
      _ ≤ _ := by simpa only [card_univ] using mul_le_mul ha hb' (pow_nonneg (by linarith) _) (by positivity)

end
end SharpLogRamsey.ActualPivot

end

end OAI
