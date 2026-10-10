import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.PredictorReverseCap
import OAI.Combinatorics.RamseyFive.Probability.PublicCapLaw

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def nextCapLaw (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (nA : ℕ) (q MA MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) :
    Law (Option (Finset (ℙ K V))) :=
  match Y with
  | none => pureLaw none
  | some Y => if hY : ValidCap B UB MB Y then
      publicCapLaw Incident A UA (B∩Y) Y
        ((hY.source_nonempty hB).mono Finset.inter_subset_right) nA q MA
    else pureLaw none

theorem geometric_two_public_caps {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : 3≤Nat.card K) (A UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAU : A⊆UA)
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBU : B⊆UB)
    (W : Finset (ℙ K V)) (hW : W.Nonempty) (c : ℝ) (hc : 0<c) (hc9 : c≤9/10)
    (hcapture : c*A.card≤(A∩W).card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤c*A.card*B.card)
    (nA nB : ℕ) (hnA : 0<nA) (hnB : 0<nB)
    (hlenA : 20*(Nat.card K:ℝ)*Real.log ((UA.card:ℝ)/A.card)≤nA)
    (hlenB : 20*(Nat.card K:ℝ)*Real.log ((UB.card:ℝ)/B.card)≤nB) :
    let q : ℝ := Nat.card K
    let MA := (320/((9:ℝ)/10)+320)*q^(d+1)/B.card
    let MB := (320/c+320)*q^(d+1)/A.card
    let firstCap := publicCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB
    let p := adaptiveLaw firstCap (nextCapLaw A UA B UB hB nA q MA MB)
    eventMass p (Finset.univ.filter fun caps=>caps.1=none ∨ caps.2=none)≤2*Real.exp (-q) ∧
    first p=firstCap ∧
    (∀Y,0 < firstCap (some Y) → ValidCap B UB MB Y) ∧
    (∀Y Z,0 < p (some Y,some Z) → ValidCap B UB MB Y ∧ ValidCap A UA MA Z) := by
  dsimp only
  let q : ℝ := Nat.card K
  let MA := (320/((9:ℝ)/10)+320)*q^(d+1)/B.card
  let MB := (320/c+320)*q^(d+1)/A.card
  let firstCap := publicCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB
  let next := nextCapLaw A UA B UB hB nA q MA MB
  have hC : (A∩W).Nonempty := by
    apply Finset.card_pos.mp
    have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
    have : (0:ℝ)<(A∩W).card := lt_of_lt_of_le (mul_pos hc ha) hcapture
    exact_mod_cast this
  have hc1 : c≤1 := by linarith
  have hfirst : firstCap none≤Real.exp (-q) := by
    apply publicCapLaw_failure _ _ _ _ _ hC hW Finset.inter_subset_right
    apply geometric_dual_validation_mass hdim hd hq B UB hB hBU A (A∩W) hC
      Finset.inter_subset_left c hc hc1 hcapture _ nB hnB hlenB
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hsparse
  have hgood (Y) (hY : 0 < firstCap (some Y)) : ValidCap B UB MB Y :=
    publicCapLaw_positive _ _ _ _ _ _ _ _ _ _ hY
  have hsparse' : 1000*q*incidences A B≤(9:ℝ)/10*A.card*B.card := by
    have hh := mul_le_mul_of_nonneg_right hc9
      (show (0:ℝ)≤(A.card:ℝ)*B.card by positivity)
    dsimp [q]
    nlinarith
  have hnext (Y) (hY : 0 < firstCap (some Y)) : next (some Y) none≤Real.exp (-q) := by
    have hvalid := hgood Y hY
    dsimp only [next,nextCapLaw]
    rw [dite_eq_left hvalid]
    apply publicCapLaw_failure _ _ _ _ _ (hvalid.source_nonempty hB) _ Finset.inter_subset_right
    exact geometric_validation_mass hdim hd hq A UA hA hAU B (B∩Y)
      (hvalid.source_nonempty hB) Finset.inter_subset_left ((9:ℝ)/10)
      (by norm_num) (by norm_num) hvalid.2.2 hsparse' nA hnA hlenA
  refine ⟨?_,adaptiveLaw_first _ _,hgood,?_⟩
  · have hh := adaptive_option_failure firstCap next (Real.exp (-q)) (Real.exp (-q))
      (Real.exp_pos _).le hfirst hnext
    simpa only [two_mul] using hh
  · intro Y Z hYZ
    change 0<firstCap (some Y)*next (some Y) (some Z) at hYZ
    have hypos : 0 < firstCap (some Y) := by
      by_contra hh
      have hz : firstCap (some Y)=0 := le_antisymm (le_of_not_gt hh) (firstCap.nonneg _)
      rw [hz,zero_mul] at hYZ
      exact lt_irrefl _ hYZ
    have hzpos : 0 < next (some Y) (some Z) := by
      by_contra hh
      have hz : next (some Y) (some Z)=0 := le_antisymm (le_of_not_gt hh) ((next _).nonneg _)
      rw [hz,mul_zero] at hYZ
      exact lt_irrefl _ hYZ
    have hvalid := hgood Y hypos
    refine ⟨hvalid,?_⟩
    dsimp only [next,nextCapLaw] at hzpos
    rw [dite_eq_left hvalid] at hzpos
    exact publicCapLaw_positive _ _ _ _ _ _ _ _ _ _ hzpos

end SharpRamseyFive.ProjectiveIncidence

end OAI
