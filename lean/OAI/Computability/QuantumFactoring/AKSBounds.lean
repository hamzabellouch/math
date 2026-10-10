import Mathlib
import OAI.Computability.QuantumFactoring.BoundedAKS

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

abbrev aksBranchBound (n s w : ℕ) :=
  216*w*w+154*w+27+1 + (n^2*(100*w+23+w*(3672*w*w+436*w+36))+1) +
  (8*s*(216*w*w+203*w+38)+1) + (8*s*(cyclicTestBound s w+1)+1) + 3

lemma aksBranch_count (n s : ℕ) [NeZero s] :
    (aksBranch n s).net.count ≤ aksBranchBound n s (rootWidth n) := by
  have hd := dividesNet_count (rootWidth n) s
  have ho := orderTests_count (rootWidth n) s (n^2)
  have hs := noSmallDivisor_count (rootWidth n) (8*s)
  have hc := allCongruences_count s (rootWidth n)
  have hmul : (8*s-1)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) ≤
      (8*s)*(216*rootWidth n*rootWidth n+203*rootWidth n+38) := by gcongr; omega
  simp only [aksBranch,count_band,count_bnot]
  dsimp [aksBranchBound]
  omega

lemma aksBranchBound_mono {n s s' w : ℕ} (hs : s ≤ s') :
    aksBranchBound n s w ≤ aksBranchBound n s' w := by
  unfold aksBranchBound
  gcongr
  exact cyclicTestBound_mono hs le_rfl

lemma aksStaticBranch_count (n s : ℕ) (hs : s ≤ n^8) :
    (aksStaticBranch n s).net.count ≤ aksBranchBound n (n^8) (rootWidth n) := by
  by_cases hp : s.Prime
  · let : NeZero s := ⟨hp.ne_zero⟩
    have he : aksStaticBranch n s = aksBranch n s := dite_eq_left hp
    exact (congrArg (fun c : BooleanNetwork (rootWidth n) 1 => c.net.count) he).trans_le
      ((aksBranch_count n s).trans (aksBranchBound_mono hs))
  · have he : aksStaticBranch n s = constant false := dite_eq_right hp
    rw [he]
    change 1 ≤ aksBranchBound n (n^8) (rootWidth n)
    unfold aksBranchBound
    omega

abbrev primalityBound (n : ℕ) :=
  (n+1)*(perfectCheckBound n+4)+1+1 +
  ((n^8+1)*(aksBranchBound n (n^8) (rootWidth n)+4)+1)+1

/-- Explicit polynomial size for the full exact primality network. -/
theorem primalityNet_count (n : ℕ) : (primalityNet n).net.count ≤ primalityBound n := by
  have hp := perfectPowerNet_count n
  have ha := any_count (c := aksBranchBound n (n^8) (rootWidth n))
    (List.ofFn (fun s : Fin (n^8+1) => aksStaticBranch n s.val)) (by
      intro c hc
      obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hc
      exact aksStaticBranch_count n s.val (by omega))
  simp only [List.length_ofFn] at ha
  simp only [primalityNet,count_band,count_bnot]
  dsimp [primalityBound]
  omega

end ExactQuantumFactoring.BitArithmetic


end

end OAI
