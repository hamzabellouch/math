import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.PredictorReverseCap
import OAI.Combinatorics.RamseyFive.Probability.AmbientPublicTest

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem geometric_ambient_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (X X₀ C W : Finset (ℙ K (Dual K V))) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCX : C⊆X) (hCW : C⊆W) (hXX₀ : X⊆X₀)
    (c γ : ℝ) (hc : 0<c) (hc1 : c≤1) (hγ : 0<γ)
    (hcapture : c*X.card≤C.card) (htrim : γ*X₀.card≤X.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences S X≤c*S.card*X.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n)
    (a : ℙ K V)  :
    eventMass (ambientCapLaw Incident S U C W hW n (Nat.card K)
      ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) (Finset.univ.filter (Excludes a))≤
      (50*(Nat.card K:ℝ)/(9*(c*γ)))*(((X₀.filter (Incident a)).card:ℝ)/X₀.card) := by
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  have hsize : (c*γ)*X₀.card≤C.card := by
    calc
      _ = c*(γ*X₀.card) := by ring
      _ ≤ c*X.card := mul_le_mul_of_nonneg_left htrim hc.le
      _ ≤ _ := hcapture
  exact ambientCapLaw_domination Incident S U C X₀ W hC hW hCW (hCX.trans hXX₀)
    n hn (Nat.card K) (c*γ) _ hq0 (mul_pos hc hγ) hsize
    (geometric_validation_mass hdim hd hq S U hS hSU X C hC hCX c hc hc1 hcapture hsparse n hn hlen) a

theorem geometric_dual_ambient_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (S U : Finset (ℙ K (Dual K V))) (hS : S.Nonempty) (hSU : S⊆U)
    (X X₀ C W : Finset (ℙ K V)) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCX : C⊆X) (hCW : C⊆W) (hXX₀ : X⊆X₀)
    (c γ : ℝ) (hc : 0<c) (hc1 : c≤1) (hγ : 0<γ)
    (hcapture : c*X.card≤C.card) (htrim : γ*X₀.card≤X.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences X S≤c*S.card*X.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((U.card:ℝ)/S.card)≤n)
    (a : ℙ K (Dual K V))  :
    eventMass (ambientCapLaw (fun a b=>Incident b a) S U C W hW n (Nat.card K)
      ((320/c+320)*(Nat.card K:ℝ)^(d+1)/X.card)) (Finset.univ.filter (Excludes a))≤
      (50*(Nat.card K:ℝ)/(9*(c*γ)))*(((X₀.filter (fun b=>Incident b a)).card:ℝ)/X₀.card) := by
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  have hsize : (c*γ)*X₀.card≤C.card := by
    calc
      _ = c*(γ*X₀.card) := by ring
      _ ≤ c*X.card := mul_le_mul_of_nonneg_left htrim hc.le
      _ ≤ _ := hcapture
  exact ambientCapLaw_domination (fun a b=>Incident b a) S U C X₀ W hC hW hCW (hCX.trans hXX₀)
    n hn (Nat.card K) (c*γ) _ hq0 (mul_pos hc hγ) hsize
    (geometric_dual_validation_mass hdim hd hq S U hS hSU X C hC hCX c hc hc1 hcapture hsparse n hn hlen) a

end SharpRamseyFive.ProjectiveIncidence

end OAI
