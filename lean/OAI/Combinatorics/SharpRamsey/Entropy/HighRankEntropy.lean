import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRankContext

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Selection
open scoped Classical BigOperators
noncomputable section
variable {K V Ω : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype Ω]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_bound {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (Fintype.card (Projectivization K V):ℝ)≤2*(Nat.card K:ℝ)^d := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  simp only [Nat.cast_pow]
  exact HighRankExcess.geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K)) d

omit [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card_positive {d : ℕ} (hdim : Module.finrank K V=d+1) :
    (0:ℝ)<Fintype.card (Projectivization K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim,Nat.cast_sum]
  apply lt_of_lt_of_le (by norm_num : (0:ℝ)<(Nat.card K^0:ℕ))
  exact single_le_sum (fun i _=>Nat.cast_nonneg _) (mem_range.mpr (by omega))

omit [FiniteDimensional K V] in
lemma flag_card_log {d : ℕ} (hdim : Module.finrank K V=d+1) :
    log (Fintype.card (Projectivization K (Module.Dual K V)×Projectivization K V))≤
      2*(log 2+(d:ℝ)*log (Nat.card K)) := by
  have hdual : Module.finrank K (Module.Dual K V)=d+1 := by rw [Subspace.dual_finrank_eq,hdim]
  have ha:=projective_card_bound hdual
  have hb:=projective_card_bound hdim
  have hap:=projective_card_positive hdual
  have hbp:=projective_card_positive hdim
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Finite.card_pos
  simp only [Fintype.card_prod,Nat.cast_mul]
  apply (log_le_log (mul_pos hap hbp)
    (mul_le_mul ha hb hbp.le (by positivity))).trans
  rw [←pow_two,log_pow,log_mul (by norm_num) (pow_ne_zero _ hq.ne'),log_pow]
  rfl

omit [FiniteDimensional K V] in
theorem raw_entropy {d h : ℕ} (hdim : Module.finrank K V=d+1)
    (p : Law Ω)
    (code : Ω→(Fin h→Projectivization K (Module.Dual K V)×Projectivization K V)×
      (Fin h→Projectivization K (Module.Dual K V)×Projectivization K V)) :
    entropy (p.map code)≤4*(h:ℝ)*(log 2+(d:ℝ)*log (Nat.card K)) := by
  apply (raw_rows_entropy h p code).trans
  have hh:=mul_le_mul_of_nonneg_left (flag_card_log hdim) (by positivity : 0≤2*(h:ℝ))
  convert hh using 1
  ring

end
end SharpLogRamsey.ActualHighRank

end

end OAI
