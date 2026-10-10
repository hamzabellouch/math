import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.UniformCutoff
import OAI.Combinatorics.RamseyFive.Entropy.SubsetEncoding

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding CellVariance ScoreRegularity
open scoped Classical LinearAlgebra.Projectivization BigOperators NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_small_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : (n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=Fintype.card (Alphabet U n) := by
  calc
    _ = Fintype.card (Fin (Fintype.card (Alphabet U n))) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_true]))
    _ = _ := Fintype.card_fin _

omit [Finite K] [FiniteDimensional K V] in
lemma baseAlphabet_large_card (U : Finset (ℙ K V)) (n : ℕ) (P τ : ℝ)
    (hn : ¬(n:ℝ)≤100*(Nat.card K:ℝ)*P) :
    Fintype.card (baseAlphabet U n P τ)=
      sizeScoreCutoff U n P τ*(Fintype.card (ℙ K (Dual K V))+1) := by
  calc
    _ = Fintype.card (Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1)) :=
      Fintype.card_congr (Equiv.cast (by simp only [baseAlphabet,hn,ite_false]))
    _ = _ := by rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

omit [FiniteDimensional K V] in
theorem baseAlphabet_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) :
    Real.log (Fintype.card (baseAlphabet U S.card P τ):ℝ)≤
      100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  have hqN : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast hqN
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hp : 0≤P := by linarith
  have hgap : 0≤Real.log ((U.card:ℝ)/S.card) := Real.log_nonneg ((le_div_iff₀ hs).mpr (by
    simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  by_cases hn : (S.card:ℝ)≤100*(Nat.card K:ℝ)*P
  · rw [baseAlphabet_small_card U _ P τ hn]
    apply (small_set_description S U hSU (Nat.card K:ℝ) P hn).2.trans
    apply mul_le_mul_of_nonneg_left (by linarith : Real.log ((U.card:ℝ)/S.card)+1≤
      Real.log ((U.card:ℝ)/S.card)+P)
    positivity
  · rw [baseAlphabet_large_card U _ P τ hn,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hN : 0<sizeScoreCutoff U S.card P τ := scoreCutoff_pos S U P τ
    have hD : (0:ℝ)<Fintype.card (ℙ K (Dual K V))+1 := by positivity
    rw [Real.log_mul (by exact_mod_cast Nat.ne_of_gt hN) hD.ne']
    have hA := scoreSearchCost_nonneg S U hS hSU P τ hp hτ
    have hl := FiniteEntropy.ceil_ratio_log (Nat.card K:ℝ)
      (Real.exp (-scoreSearchCost S U P τ)) (by linarith) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
    rw [Real.log_exp,sub_neg_eq_add] at hl
    have hlogN : Real.log (sizeScoreCutoff U S.card P τ)≤
        Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ := by
      simpa only [sizeScoreCutoff,scoreSearchCost,Real.exp_neg,div_inv_eq_mul] using hl
    have hlogD : Real.log (Fintype.card (ℙ K (Dual K V))+1:ℝ)≤
        Real.log (2*(Nat.card K:ℝ)^2) := by
      apply Real.log_le_log hD
      rw [card_hyperplanes (d:=2) hdim]
      have hh := Q_le_two_pow (Nat.card K) 2 hqN
      linarith
    have hscalar := base_cost_scalar (Nat.card K:ℝ) P (Real.log ((U.card:ℝ)/S.card)) τ
      hq hP hgap hτ hτ1
    unfold scoreSearchCost at hlogN
    have hlast : 0≤(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by positivity
    nlinarith

end SharpRamseyFive.ScoreGeometry

end OAI
