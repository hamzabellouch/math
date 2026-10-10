import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalEstimator

namespace OAI

namespace MatchingFPRAS.FiniteTrial
variable {G : GraphInput} [Nontrivial (Fin G.n)]
def sampleCount (p : Trial.Parameters G) : ℕ :=
  ⌈10*(Counting.sigma (sourceD (G:=G) p.K) p.K p.epsilon)⁻¹^2*((G.n:ℚ)+p.K+1)⌉₊
omit [Nontrivial (Fin G.n)] in
lemma sampleCount_eq (p : Trial.Parameters G) : sampleCount p=p.S := by
  unfold sampleCount Trial.Parameters.S Enlargement.stageSampleCount
  apply Nat.ceil_congr
  intro s
  unfold Trial.Parameters.D
  rw [←sourceD_eq (G:=G)]
  have hh:=Counting.sigma_cast (sourceD (G:=G) p.K) p.K p.epsilon
  rw [←hh]
  exact_mod_cast Iff.rfl
end MatchingFPRAS.FiniteTrial

end OAI
