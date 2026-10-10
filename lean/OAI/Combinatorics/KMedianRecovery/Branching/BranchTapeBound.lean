import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchSeedLayout

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchTape
attribute [local irreducible] Categorical.Explicit.exponent Categorical.Explicit.samples Categorical.Explicit.steps
lemma count_bound {n b p H : ℕ} (hn : n≤H) (hb : b≤H) (hp : p≤H) :
    count n b p ≤ 201326592000000015*(H+2)^12 := by
  let X := H+2
  have hX : 1≤X := by dsimp [X]; omega
  have hnX : n≤X := hn.trans (by dsimp [X];omega)
  have hbX : b≤X := hb.trans (by dsimp [X];omega)
  have hpX : p≤X := hp.trans (by dsimp [X];omega)
  have hpn : p*n≤X^2 := by
    calc p*n≤X*X := Nat.mul_le_mul hpX hnX
         _=X^2 := by ring
  have hpn1 : p*n+1≤X^2 := by
    have hh:=Nat.mul_le_mul hp hn
    dsimp [X]
    nlinarith
  have hstep : Categorical.Explicit.steps p≤4096*X^2 :=
    (Categorical.Explicit.steps_upper p).trans (by dsimp [X];gcongr)
  have hexp : Categorical.Explicit.exponent p≤12*X := by
    have hr : (p+1).size≤p+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    unfold Categorical.Explicit.exponent
    dsimp [X]
    omega
  have hp1 : p+1≤X := by dsimp [X];omega
  have hsamp : Categorical.Explicit.samples (p*n) p≤4096000000000*X^6 := by
    unfold Categorical.Explicit.samples
    calc
      _ ≤ 1000000000*(4096*X^2)*X^2*X^2 := by gcongr
      _ = _ := by ring
  have hm : BinaryCategorical.Tape.M (p*n) p (Categorical.Explicit.exponent p)
      (Categorical.Explicit.samples (p*n) p) ≤ 201326592000000000*X^12 := by
    unfold BinaryCategorical.Tape.M BinarySeed.count
    change 2^Categorical.Explicit.exponent p*((p*n)*(Categorical.Explicit.samples (p*n) p*(p*Categorical.Explicit.exponent p))) ≤ _
    rw [←Categorical.Explicit.steps]
    calc
      _ ≤ (4096*X^2)*(X^2*((4096000000000*X^6)*(X*(12*X)))) := by gcongr
      _ = _ := by ring
  have hk : BinaryCategorical.Tape.K p (Categorical.Explicit.exponent p)≤12*X^2 := by
    unfold BinaryCategorical.Tape.K BinarySeed.count
    calc p*Categorical.Explicit.exponent p≤X*(12*X) := Nat.mul_le_mul hpX hexp
         _=12*X^2 := by ring
  have hl : labelCount n b≤X^2 := by
    unfold labelCount
    calc n*Nat.clog 2 b≤X*X := Nat.mul_le_mul hnX ((Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=b)).le).trans hbX)
         _=X^2 := by ring
  have hc : colorCount n≤2*X := by unfold colorCount;omega
  have hpow1 : X≤X^12 := by
    calc X=X^1 := by simp
         _≤X^12 := Nat.pow_le_pow_right hX (by decide)
  have hpow2 : X^2≤X^12 := Nat.pow_le_pow_right hX (by decide)
  unfold count completionCount
  dsimp [X] at *
  omega
end MetricKMedianRecovery.BitMachine.BinaryBranchTape

end OAI
