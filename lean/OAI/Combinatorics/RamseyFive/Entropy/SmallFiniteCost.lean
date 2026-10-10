import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BaseFiniteCost

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem smallFinite_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) :
    baseFiniteCost U P τ m≤110*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  unfold baseFiniteCost
  rw [baseFinite_header S U P τ t m hm,baseAlphabet_small_card U S.card P τ hn]
  have hcost := (small_set_description S U hSU (Nat.card K:ℝ) P hn).2
  have hh := projective_header_le σ hσ hq hd
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg
    ((le_div_iff₀ (by exact_mod_cast hS.card_pos)).mpr (by
      simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  have htotal : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
    apply (le_mul_of_one_le_right (by positivity) hP).trans
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have hcost' : 100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+1)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith only [hcost,hh,htotal,hcost']
end SharpRamseyFive.ScoreGeometry

end OAI
