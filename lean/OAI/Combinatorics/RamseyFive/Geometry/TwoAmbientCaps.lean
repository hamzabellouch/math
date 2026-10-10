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

noncomputable def nextAmbientCapLaw (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (nA : ℕ) (q MA MB : ℝ) (Y : Option (Finset (ℙ K (Dual K V)))) :
    Law (Option (Finset (ℙ K V))) :=
  match Y with
  | none => pureLaw none
  | some Y => if hY : ValidCap B UB MB (UB∩Y) then
      ambientCapLaw Incident A UA (B∩(UB∩Y)) (UB∩Y)
        ((hY.source_nonempty hB).mono Finset.inter_subset_right) nA q MA
    else pureLaw none

theorem geometric_two_ambient_caps {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
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
    let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB
    let p := adaptiveLaw firstCap (nextAmbientCapLaw A UA B UB hB nA q MA MB)
    eventMass p (Finset.univ.filter fun caps=>caps.1=none ∨ caps.2=none)≤2*Real.exp (-q) ∧
    first p=firstCap ∧
    (∀Y,0 < firstCap (some Y) → ValidCap B UB MB (UB∩Y)) ∧
    (∀Y Z,0 < p (some Y,some Z) → ValidCap B UB MB (UB∩Y) ∧ ValidCap A UA MA (UA∩Z)) := by
  dsimp only
  let q : ℝ := Nat.card K
  let MA := (320/((9:ℝ)/10)+320)*q^(d+1)/B.card
  let MB := (320/c+320)*q^(d+1)/A.card
  let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB
  let next := nextAmbientCapLaw A UA B UB hB nA q MA MB
  have hC : (A∩W).Nonempty := by
    apply Finset.card_pos.mp
    have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
    have : (0:ℝ)<(A∩W).card := lt_of_lt_of_le (mul_pos hc ha) hcapture
    exact_mod_cast this
  have hc1 : c≤1 := by linarith
  have hfirst : firstCap none≤Real.exp (-q) := by
    rw [ambientCapLaw_none]
    apply publicCapLaw_failure _ _ _ _ _ hC hW Finset.inter_subset_right
    apply geometric_dual_validation_mass hdim hd hq B UB hB hBU A (A∩W) hC
      Finset.inter_subset_left c hc hc1 hcapture _ nB hnB hlenB
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hsparse
  have hgood (Y) (hY : 0 < firstCap (some Y)) : ValidCap B UB MB (UB∩Y) :=
    ambientCapLaw_positive _ _ _ _ _ _ _ _ _ _ hY
  have hsparse' : 1000*q*incidences A B≤(9:ℝ)/10*A.card*B.card := by
    have hh := mul_le_mul_of_nonneg_right hc9
      (show (0:ℝ)≤(A.card:ℝ)*B.card by positivity)
    dsimp [q]
    nlinarith
  have hnext (Y) (hY : 0 < firstCap (some Y)) : next (some Y) none≤Real.exp (-q) := by
    have hvalid := hgood Y hY
    dsimp only [next,nextAmbientCapLaw]
    rw [dite_eq_left hvalid]
    rw [ambientCapLaw_none]
    apply publicCapLaw_failure _ _ _ _ _ (hvalid.source_nonempty hB) _ Finset.inter_subset_right
    exact geometric_validation_mass hdim hd hq A UA hA hAU B (B∩(UB∩Y))
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
    dsimp only [next,nextAmbientCapLaw] at hzpos
    rw [dite_eq_left hvalid] at hzpos
    exact ambientCapLaw_positive _ _ _ _ _ _ _ _ _ _ hzpos


lemma incidence_density_le {d : ℕ} (hd : 1≤d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d≤1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  rw [one_mul,Q_recurrence hd]
  push_cast
  nlinarith

lemma reciprocal_rectangle_flags (hdim : finrank K V=5)
    (U : Finset (ℙ K V)) (W : Finset (ℙ K (Dual K V)))
    (C b : ℝ) (hC : 1≤C) (hb : 0≤b)
    (hprod : (U.card:ℝ)*W.card≤C*(Nat.card K:ℝ)^5*Real.exp b) :
    (incidences U W:ℝ)≤2*C*(Nat.card K:ℝ)^4*Real.exp b := by
  let q : ℝ := Nat.card K
  have hq : 0<q := by dsimp [q];exact_mod_cast Nat.card_pos (α:=K)
  have hmix := incidence_mixing (d:=4) hdim (by norm_num) U W
  norm_num only [Nat.reduceSub] at hmix
  have hden := incidence_density_le (K:=K) (d:=4) (by norm_num)
  norm_num only [Nat.reduceSub] at hden
  have hmean := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hden
    (show (0:ℝ)≤U.card by positivity)) (show (0:ℝ)≤W.card by positivity)
  have hmain : (1/q)*(U.card:ℝ)*W.card≤C*q^4*Real.exp b := by
    rw [show (1/q)*(U.card:ℝ)*W.card=((U.card:ℝ)*W.card)/q by ring]
    apply (div_le_iff₀ hq).mpr
    simpa only [show C*q^4*Real.exp b*q=C*q^5*Real.exp b by ring] using hprod
  have hcb : 1≤C*Real.exp b := by
    have he : 1≤Real.exp b := Real.one_le_exp_iff.mpr hb
    nlinarith
  have hcb2 : C*Real.exp b≤(C*Real.exp b)^2 := by nlinarith
  have hbase := mul_le_mul_of_nonneg_left hprod (pow_nonneg hq.le 3)
  have hupper := mul_le_mul_of_nonneg_left hcb2 (pow_nonneg hq.le 8)
  have hsquare : q^3*(U.card:ℝ)*W.card≤(C*q^4*Real.exp b)^2 := by
    dsimp [q] at hbase
    nlinarith only [hbase,hupper]
  have hsqrt : Real.sqrt (q^3*(U.card:ℝ)*W.card)≤C*q^4*Real.exp b :=
    (Real.sqrt_le_left (by positivity)).mpr hsquare
  have hm := le_abs_self ((incidences U W:ℝ)-
    (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card)
  change |(incidences U W:ℝ)-
    (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card|≤
      Real.sqrt (q^3*(U.card:ℝ)*W.card) at hmix
  change (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*U.card*W.card≤(1/q)*U.card*W.card at hmean
  linarith

lemma reciprocal_cap_product (Q a b x y C D loss : ℝ)
    (hQ : 0<Q) (ha : 0<a) (hb : 0<b) (_hx : 0≤x) (hy : 0≤y)
    (hC : 0≤C) (hD : 0≤D) (hp : Q*Real.exp (-loss)≤a*b)
    (hxc : x≤C*Q/b) (hyc : y≤D*Q/a) :
    x*y≤C*D*Q*Real.exp loss := by
  have hx' := (le_div_iff₀ hb).mp hxc
  have hy' := (le_div_iff₀ ha).mp hyc
  have hxy := mul_le_mul hx' hy' (mul_nonneg hy ha.le) (mul_nonneg hC hQ.le)
  have hp' : Q≤a*b*Real.exp loss := by
    have hh := mul_le_mul_of_nonneg_right hp (Real.exp_pos loss).le
    rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left hp' (mul_nonneg hC hD)
  have hh' := mul_le_mul_of_nonneg_right hh hQ.le
  have hab : 0<a*b := mul_pos ha hb
  apply (mul_le_mul_iff_left₀ hab).mp
  nlinarith only [hxy,hh']

theorem validated_caps_flags (hdim : finrank K V=5)
    (A UA Z : Finset (ℙ K V)) (B UB Y : Finset (ℙ K (Dual K V)))
    (hA : A.Nonempty) (hB : B.Nonempty) (c b : ℝ) (hc : 0<c) (hb : 0≤b)
    (hprod : (Nat.card K:ℝ)^5*Real.exp (-b)≤(A.card:ℝ)*B.card)
    (hZ : ValidCap A UA ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card) Z)
    (hY : ValidCap B UB ((320/c+320)*(Nat.card K:ℝ)^5/A.card) Y) :
    (incidences Z Y:ℝ)≤
      2*((320/((9:ℝ)/10)+320)*(320/c+320))*(Nat.card K:ℝ)^4*Real.exp b := by
  have hconst : 1≤(320/((9:ℝ)/10)+320)*(320/c+320) := by
    have : 0≤320/c := by positivity
    nlinarith
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  apply reciprocal_rectangle_flags hdim Z Y _ b hconst hb
  exact reciprocal_cap_product ((Nat.card K:ℝ)^5) A.card B.card Z.card Y.card
      (320/((9:ℝ)/10)+320) (320/c+320) b (pow_pos hq _)
      (by exact_mod_cast hA.card_pos) (by exact_mod_cast hB.card_pos)
      (by positivity) (by positivity) (by norm_num) (by positivity) hprod hZ.2.1 hY.2.1

end SharpRamseyFive.ProjectiveIncidence

end OAI
