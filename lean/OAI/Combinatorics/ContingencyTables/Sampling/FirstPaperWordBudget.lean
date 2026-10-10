import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperOuterBudget

namespace OAI

/-! # A polynomial bound for the full first-paper Boolean word -/

namespace ContingencyTables

/-- Each outer trial contains a small walk and a fresh completion word. -/
def smallSamplerWordBudget (d b k : ℕ) : ℕ :=
  let f := 25*(d+b+outerAccuracy d b k+1)^62
  outerTrials d k*(outerSteps d b k*(Nat.clog 2 (32*d^2)+f)+f)

private lemma double_power_le {S : ℕ} (hS : 2 ≤ S) (n : ℕ) :
    2*S^n ≤ S^(n+1) := by
  rw [pow_succ']
  exact Nat.mul_le_mul_right _ hS

private lemma one_mul_power (S a b : ℕ) : S*(S^a)^b=S^(a*b+1) := by
  rw [←pow_mul,pow_succ']

private lemma natPower_mul (S a b c : ℕ) (hc : a+b=c) : S^a*S^b=S^c := by
  rw [←pow_add,hc]

private lemma natPower_mono (S i j : ℕ) (hS : 1 ≤ S) (hij : i ≤ j) : S^i ≤ S^j :=
  Nat.pow_le_pow_right hS hij

private theorem wordBudget_bound (d b k S : ℕ) (hinput : d+b+k+100 ≤ S) :
    smallSamplerWordBudget d b k ≤ S^644 := by
  have hS : 2 ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  have hd : d ≤ S := by omega
  have hb : k+b ≤ S := by omega
  have hk : k+1 ≤ S := by omega
  have hn : outerSteps d b k ≤ S^202 := by
    unfold outerSteps
    calc
      _ ≤ S^200*S^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
      _ = _ := (pow_add S 200 2).symm
  have hh : outerAccuracy d b k ≤ S^6 := by
    unfold outerAccuracy
    calc
      _ ≤ S^4*S^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
      _ = _ := (pow_add S 4 2).symm
  have hlin : d+b+outerAccuracy d b k+1 ≤ S^7 := by
    have hp := Nat.le_self_pow (by decide : 6≠0) S
    exact (show d+b+outerAccuracy d b k+1 ≤ 2*S^6 by omega).trans (double_power_le hS 6)
  have hf : 25*(d+b+outerAccuracy d b k+1)^62 ≤ S^435 := by
    have hm := Nat.mul_le_mul (show 25 ≤ S by omega) (Nat.pow_le_pow_left hlin 62)
    have he := one_mul_power S 7 62
    have hp : S^(7*62+1)=S^435 := congrArg (fun n => S^n) (by decide)
    exact hm.trans_eq (he.trans hp)
  have hs : Nat.clog 2 (32*d^2) ≤ S^3 := by
    calc
      _ ≤ 32*d^2 := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
      _ ≤ S*S^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hd _)
      _ = _ := (pow_succ' S 2).symm
  have hsum : Nat.clog 2 (32*d^2)+25*(d+b+outerAccuracy d b k+1)^62 ≤ S^436 := by
    have hp : S^3 ≤ S^435 := natPower_mono S 3 435 hS1 (by decide)
    calc
      _ ≤ S^435+S^435 := Nat.add_le_add (hs.trans hp) hf
      _ = 2*S^435 := (two_mul _).symm
      _ ≤ S^(435+1) := double_power_le hS 435
      _ = S^436 := congrArg (fun n => S^n) (by decide)
  have hinner : outerSteps d b k*(Nat.clog 2 (32*d^2)+25*(d+b+outerAccuracy d b k+1)^62)+
      25*(d+b+outerAccuracy d b k+1)^62 ≤ S^639 := by
    have hp : S^435 ≤ S^638 := natPower_mono S 435 638 hS1 (by decide)
    calc
      _ ≤ S^638+S^638 := Nat.add_le_add
        ((Nat.mul_le_mul hn hsum).trans_eq (natPower_mul S 202 436 638 (by decide))) (hf.trans hp)
      _ = 2*S^638 := (two_mul _).symm
      _ ≤ S^(638+1) := double_power_le hS 638
      _ = S^639 := congrArg (fun n => S^n) (by decide)
  have hJ : outerTrials d k ≤ S^5 := by
    unfold outerTrials
    calc
      _ ≤ S^4*S := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hk
      _ = _ := (pow_succ S 4).symm
  unfold smallSamplerWordBudget
  exact (Nat.mul_le_mul hJ hinner).trans_eq (natPower_mul S 5 639 644 (by decide))


theorem smallSamplerWordBudget_polynomial (d b k : ℕ) :
    smallSamplerWordBudget d b k ≤ (d+b+k+100)^644 :=
  wordBudget_bound d b k (d+b+k+100) le_rfl

end ContingencyTables

end OAI
