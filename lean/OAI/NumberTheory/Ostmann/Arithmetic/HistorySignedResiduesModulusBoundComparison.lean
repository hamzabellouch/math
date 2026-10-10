import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundSize
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusCost

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistoryCRTIntegration

theorem crtModulus_pos {l : ℕ} (h k : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hout : ∀q∈outside,Nat.Prime q) (n : ℕ) : 0<crtModulus h k outside n :=
  mul_pos (mul_pos (mul_pos (rootModulus_pos h hs) (outsideModulus_pos hout))
    (frequencyModulus_pos h k hs ks n)) (representativeModulus_pos h k hs ks)

theorem comparisonModulus_pos {l : ℕ} (h k : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hout : ∀q∈outside,Nat.Prime q) (n : ℕ) : 0<comparisonModulus h k outside n :=
  mul_pos (pairModulus_pos h k hs ks (fun q hq=>(hout q hq).pos))
    (crtModulus_pos h k hs ks hout n)

theorem comparisonModulus_log_le {N C : ℕ} {B : ℝ} (hB : 1≤B) {l : ℕ}
    (h k : History l) (hh : factorBound N B h) (hk : factorBound N B k)
    (outside : List ℕ) (hlen : outside.length≤N) (hout : ∀q∈outside,(q:ℝ)≤B)
    (n : ℕ) (hp : 0<pairModulus h k outside) (hc : 0<crtModulus h k outside n)
    (hcrt : (crtModulus h k outside n:ℝ) ≤ B^(C*(N+1))) :
    Real.log (comparisonModulus h k outside n) ≤
      ((pairedCostCoefficient l+C:ℕ):ℝ)*((N:ℝ)+1)*Real.log B := by
  have hp' : (0:ℝ)<pairModulus h k outside := by exact_mod_cast hp
  have hc' : (0:ℝ)<crtModulus h k outside n := by exact_mod_cast hc
  have hcost := pairedCost_le h k hh hk outside hlen
  have hcost' : ((l*(divisorCost h+divisorCost k)+testCost h+testCost k+outside.length:ℕ):ℝ) ≤
      (pairedCostCoefficient l:ℝ)*((N:ℝ)+1) := by exact_mod_cast hcost
  simp only [Nat.cast_add,Nat.cast_mul] at hcost'
  have hpair := (log_pairModulus_le hB h k hh hk outside hout hp).trans
    (mul_le_mul_of_nonneg_right hcost' (Real.log_nonneg hB))
  have hcrtlog := Real.log_le_log hc' hcrt
  rw [Real.log_pow] at hcrtlog
  have hsum := add_le_add hpair hcrtlog
  simpa only [comparisonModulus,Nat.cast_mul,Real.log_mul hp'.ne' hc'.ne',
    Nat.cast_add,Nat.cast_one,add_mul] using hsum

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
