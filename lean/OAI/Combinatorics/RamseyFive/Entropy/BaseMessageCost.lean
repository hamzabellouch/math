import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BaseAlphabetCost

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding CellVariance ScoreRegularity
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] in
theorem baseMessage_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)+
      Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      110*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  have hqN : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast hqN
  have hqp : (0:ℝ)<Nat.card K := by linarith
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg ((le_div_iff₀ hs).mpr (by
    simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  have hheader : Real.log (Fintype.card (ℙ K V)+1:ℝ)≤3*(Nat.card K:ℝ) := by
    have hcard : (Fintype.card (ℙ K V)+1:ℝ)≤2*(Nat.card K:ℝ)^2 := by
      rw [card_points (d:=2) hdim]
      have hh := Q_le_two_pow (Nat.card K) 2 hqN
      linarith
    have hh := Real.log_le_log (by positivity : (0:ℝ)<Fintype.card (ℙ K V)+1) hcard
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ hqp.ne'),Real.log_pow] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have h3 := Real.log_le_sub_one_of_pos hqp
    norm_num only [Nat.cast_ofNat] at hh
    linarith
  have hcost := baseAlphabet_cost hdim S U hS hSU P τ hP hτ hτ1
  have hprod : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
    have hp : (Nat.card K:ℝ)≤(Nat.card K:ℝ)*P := by nlinarith
    have hgap' : 1≤Real.log ((U.card:ℝ)/S.card)+P := by linarith
    exact hp.trans (le_mul_of_one_le_right (by positivity) hgap')
  nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
