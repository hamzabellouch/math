import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.TwoAmbientCaps
import OAI.Combinatorics.RamseyFive.Entropy.ChronologicalCapDomination

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem firstAmbient_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K)
    (A A₀ : Finset (ℙ K V)) (hA : A.Nonempty) (hAA₀ : A⊆A₀)
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBU : B⊆UB)
    (W : Finset (ℙ K V)) (hW : W.Nonempty)
    (c δ : ℝ) (hc : 0<c) (hc1 : c≤1) (hδ : 0<δ)
    (htrim : δ*A₀.card≤A.card) (hcapture : c*A.card≤(A∩W).card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤c*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UB.card:ℝ)/B.card)≤n)
    (b : ℙ K (Dual K V)) :
    eventMass (ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW n (Nat.card K)
      ((320/c+320)*(Nat.card K:ℝ)^(d+1)/A.card)) (Finset.univ.filter (Excludes b))≤
      (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card) := by
  have hC : (A∩W).Nonempty := by
    apply Finset.card_pos.mp
    have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
    exact_mod_cast lt_of_lt_of_le (mul_pos hc ha) hcapture
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  have hs : (c*δ)*A₀.card≤(A∩W).card := by
    have hh := mul_le_mul_of_nonneg_left htrim hc.le
    nlinarith only [hh,hcapture]
  apply ambientCapLaw_domination (fun b a=>Incident a b) B UB (A∩W) A₀ W hC hW
    Finset.inter_subset_right (Finset.inter_subset_left.trans hAA₀) n hn (Nat.card K) (c*δ) _ hq0 (mul_pos hc hδ) hs
  exact geometric_dual_validation_mass hdim hd hq B UB hB hBU A (A∩W) hC
    Finset.inter_subset_left c hc hc1 hcapture
    (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hsparse) n hn hlen

theorem secondAmbient_original {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀)
    (δ : ℝ) (hδ : 0<δ) (htrim : δ*B₀.card≤B.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card)
    (n : ℕ) (hn : 0<n) (hlen : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤n)
    (MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) (a : ℙ K V) :
    eventMass (nextAmbientCapLaw A UA B UB hB n (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^(d+1)/B.card) MB Y)
      (Finset.univ.filter (Excludes a))≤
      (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card) := by
  have hq0 : (0:ℝ)<Nat.card K := lt_of_lt_of_le (by norm_num : (0:ℝ)<3) (by exact_mod_cast hq)
  cases Y with
  | none =>
    change eventMass (pureLaw (none : Option (Finset (ℙ K V)))) (Finset.univ.filter (Excludes a))≤_
    rw [excludes_pure_none]
    positivity
  | some Y =>
    dsimp only [nextAmbientCapLaw]
    split_ifs with hY
    · have hC := hY.source_nonempty hB
      have hs : ((9:ℝ)/10*δ)*B₀.card≤(B∩(UB∩Y)).card := by
        have hh := mul_le_mul_of_nonneg_left htrim (by norm_num : (0:ℝ)≤9/10)
        nlinarith only [hh,hY.2.2]
      apply ambientCapLaw_domination Incident A UA (B∩(UB∩Y)) B₀ (UB∩Y) hC
        (hC.mono Finset.inter_subset_right) Finset.inter_subset_right (Finset.inter_subset_left.trans hBB₀)
        n hn (Nat.card K) ((9:ℝ)/10*δ) _ hq0 (by positivity) hs
      exact geometric_validation_mass hdim hd hq A UA hA hAU B (B∩(UB∩Y)) hC
        Finset.inter_subset_left (9/10) (by norm_num) (by norm_num) hY.2.2 hsparse n hn hlen
    · rw [excludes_pure_none]
      positivity
end SharpRamseyFive.ProjectiveIncidence

end OAI
