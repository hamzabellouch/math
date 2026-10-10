import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalOutput

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real ActualHighRank ExecutedPotential TreeDecoder
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]

omit [FiniteDimensional K V] in
lemma projective_log_card_add_one {d : ℕ} (hdim : Module.finrank K V=d+1)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤((d:ℝ)+2)*log (Nat.card K:ℝ) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hc:=projective_card_bound hdim
  have hp : 1≤(Nat.card K:ℝ)^d:=one_le_pow₀ hq
  have hlog : log (3:ℝ)≤2 := by
    have hh:=log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    linarith
  calc
    _ ≤ log (3*(Nat.card K:ℝ)^d) := log_le_log (by positivity) (by nlinarith)
    _ = log 3+(d:ℝ)*log (Nat.card K:ℝ) := by
      rw [log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow]
    _ ≤ _ := by nlinarith

variable [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Fintype (Projectivization K V)] [FiniteDimensional K V] in
lemma headerCost_linear {d : ℕ} (hdim : Module.finrank K V=d+3)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    headerCost (K:=K) (V:=V)≤2*((d:ℝ)+4)*log (Nat.card K:ℝ) := by
  have hdual : Module.finrank K (Module.Dual K V)=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdim]
  have hbi : Module.finrank K (Module.Dual K (Module.Dual K V))=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdual]
  have ha:=projective_log_card_add_one hdual hσ
  have hb:=projective_log_card_add_one hbi hσ
  unfold headerCost
  push_cast at ha hb
  linarith

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [FiniteDimensional K V] in
lemma root_potential_linear {d : ℕ} (hdim : Module.finrank K V=d+3)
    (hσ : 1≤log (Nat.card K:ℝ)) :
    potential ((Nat.card K:ℝ)^(d+3))
      ((univ,univ) : ChronoDomains (K:=K) (V:=V))≤2*((d:ℝ)+4)*log (Nat.card K:ℝ) := by
  have hdual : Module.finrank K (Module.Dual K V)=(d+2)+1 := by
    rw [Subspace.dual_finrank_eq,hdim]
  have hdim' : Module.finrank K V=(d+2)+1 := hdim
  have ha:=projective_log_card_add_one hdual hσ
  have hb:=projective_log_card_add_one hdim' hσ
  have hap:=projective_card_positive hdual
  have hbp:=projective_card_positive hdim'
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  unfold potential
  simp only [card_univ]
  apply max_le
  · rw [log_div (mul_ne_zero hap.ne' hbp.ne') (pow_ne_zero _ hq.ne'),
      log_mul hap.ne' hbp.ne',log_pow]
    have ha':=log_le_log hap (show (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)≤
      (Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1 by linarith)
    have hb':=log_le_log hbp (show (Fintype.card (Projectivization K V):ℝ)≤
      (Fintype.card (Projectivization K V):ℝ)+1 by linarith)
    push_cast at ha hb ⊢
    nlinarith
  · positivity
end
end SharpLogRamsey.ActualPivot

end

end OAI
