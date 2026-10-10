import Mathlib
import OAI.NumberTheory.Jacobsthal.Estimates.SourceExtensionScale
import OAI.NumberTheory.Jacobsthal.Partitions.EdgeBinBounds
import OAI.NumberTheory.Jacobsthal.Partitions.SourceIntervalReplacement
import OAI.NumberTheory.Jacobsthal.Primes.SourcePrimeSampleBound
import OAI.NumberTheory.Jacobsthal.Sieve.CRTPrimeCost
import OAI.NumberTheory.Jacobsthal.Sieve.FrozenSieveMean
import OAI.NumberTheory.Jacobsthal.Sieve.OriginalCofactorPoints

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseSaving

theorem mean_envelope (N Q n : ℕ) (hN : 0 < N) (w U K xi delta C V : ℝ)
    (hw : 1 < w) (hU : 1 < U) (hK : 0 ≤ K) (hxi : 0 < xi) (hd : 0 < delta)
    (hC : 0 ≤ C) (hV : 0 < V)
    (hcount : xi*U/(16*Real.log U) ≤ (n : ℝ))
    (hEuler : V⁻¹ ≤ 2*Real.exp Real.eulerMascheroniConstant*Real.log w)
    (hQ : (Q : ℝ) ≤ 3*U) (hlogU : Real.log U ≤ K*Real.log w) :
    (4+8*Real.pi^2)*C*((N : ℝ)+(Q : ℝ)^2)/((n : ℝ)*delta^2*(N : ℝ)*V) ≤
      (32*(4+8*Real.pi^2)*C*K*Real.exp Real.eulerMascheroniConstant/(xi*delta^2))*(Real.log w)^2*
        (1/U+9*U/(N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hUpos : 0 < U := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hlogUpos : 0 < Real.log U := Real.log_pos hU
  have hlo : 0 < xi*U/(16*Real.log U) := by positivity
  have hn : (0 : ℝ) < n := hlo.trans_le hcount
  have hni : (n : ℝ)⁻¹ ≤ 16*Real.log U/(xi*U) := by
    have hh := (inv_le_inv₀ hn hlo).mpr hcount
    simpa only [inv_div] using hh
  have hnK : (n : ℝ)⁻¹ ≤ 16*K*Real.log w/(xi*U) := by
    apply hni.trans
    apply div_le_div_of_nonneg_right _ (mul_pos hxi hUpos).le
    nlinarith
  have hQsq : (Q : ℝ)^2 ≤ 9*U^2 := by nlinarith [show (0 : ℝ) ≤ Q from Nat.cast_nonneg Q]
  calc
    _ = ((4+8*Real.pi^2)*C/delta^2)*(((N : ℝ)+(Q : ℝ)^2)/(N : ℝ))*(n : ℝ)⁻¹*V⁻¹ := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ ((4+8*Real.pi^2)*C/delta^2)*(((N : ℝ)+9*U^2)/(N : ℝ))*
        (16*K*Real.log w/(xi*U))*(2*Real.exp Real.eulerMascheroniConstant*Real.log w) := by
      gcongr
    _ = _ := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      field_simp
      ring

theorem spectral_factor_bound (N : ℕ) (hN : 0 < N) (U rho : ℝ) (_hU : 0 < U)
    (hrho : 0 < rho) (hrhoU : rho ≤ U) (hNlower : U*rho/4 ≤ (N : ℝ)) :
    1/U+9*U/(N : ℝ) ≤ 37/rho := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 1/U ≤ 1/rho := one_div_le_one_div_of_le hrho hrhoU
  have h2 : U/(N : ℝ) ≤ 4/rho := by
    apply (div_le_div_iff₀ hNR hrho).mpr
    nlinarith
  calc
    _ = 1/U+9*(U/(N : ℝ)) := by ring
    _ ≤ 1/rho+9*(4/rho) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = _ := by ring

end ErdosInverseSaving

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving

theorem log_square_absorption (A eps : ℝ) (hA : 0 ≤ A) (heps : 0 < eps) :
    ∀ᶠ w : ℝ in atTop,A*(Real.log w)^2 ≤ w^eps := by
  have hA1 : 0 < A+1 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) heps).bound (inv_pos.mpr hA1)
  filter_upwards [hs,eventually_gt_atTop (1 : ℝ)] with w hw hw1
  have hw0 : 0 < w := by linarith
  have hh : (Real.log w)^2 ≤ (A+1)⁻¹*w^eps := by
    simpa only [Real.norm_eq_abs,Real.rpow_two,abs_of_nonneg (sq_nonneg (Real.log w)),
      abs_of_nonneg (Real.rpow_nonneg hw0.le eps)] using hw
  have hp := mul_le_mul_of_nonneg_left hh hA1.le
  have hcancel : (A+1)*((A+1)⁻¹*w^eps) = w^eps := by field_simp
  rw [hcancel] at hp
  nlinarith [sq_nonneg (Real.log w)]

end ErdosInverseSaving

end

section

namespace ErdosInverseSaving
open ErdosInverseTail ErdosInversePrimeBin

theorem common_length_bin_lower (Y p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (Qplus xi w aStar U theta : ℝ) (hqQ : (q : ℝ) ≤ Qplus)
    (hQq : Qplus ≤ (1+xi)*(q : ℝ)) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hw : 1 < w) (ha : 0 < aStar) (hwU : w ≤ U) (htheta : 0 ≤ theta)
    (hlarge : 4 ≤ w^(3*aStar/4)) (hne : (primeBin U theta).Nonempty)
    (hlen : ∀ u ∈ primeBin U theta,
      3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) :
    U*w^(3*aStar/4)/4 ≤ (commonParentLength Y p Qplus : ℝ) := by
  obtain ⟨u,hu⟩ := hne
  have hUpos : 0 < U := (by linarith : 0 < w).trans_le hwU
  have humem := (mem_primeBin hUpos.le htheta u).mp hu
  have huR : (0 : ℝ) < u := hUpos.trans humem.2.1
  have hgeo := common_length_from_log Y p q u hp hq humem.1.pos Qplus xi w aStar hqQ hQq
    hxi hxi1 hw ha (hlen u hu)
  rw [mul_div_assoc (2 : ℝ) (commonParentLength Y p Qplus : ℝ) (u : ℝ)] at hgeo
  have hlow : w^(3*aStar/4)/4 ≤ (commonParentLength Y p Qplus : ℝ)/(u : ℝ) := by nlinarith
  have hprod := (le_div_iff₀ huR).mp hlow
  have hpow : 0 ≤ w^(3*aStar/4)/4 := by positivity
  calc
    _ = (w^(3*aStar/4)/4)*U := by ring
    _ ≤ (w^(3*aStar/4)/4)*(u : ℝ) := mul_le_mul_of_nonneg_left humem.2.1.le hpow
    _ ≤ _ := hprod

end ErdosInverseSaving

end

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling
attribute [local instance] Classical.decEq

noncomputable def totalCost (P U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (s : Sample U h) : ℝ :=
  (∑ p ∈ P,primeCost U h M0 E p s)/(P.card : ℝ)

theorem totalCost_nonneg (P U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (s : Sample U h) :
    0 ≤ totalCost P U h M0 E s := by
  exact div_nonneg (Finset.sum_nonneg (fun p _ => primeCost_nonneg U h M0 E p s)) (Nat.cast_nonneg _)

theorem totalCost_average_bound (P U : Finset ℕ) (h M0 : ℕ) [NeZero M0]
    (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val)) (R tau T : ℝ)
    (hP : 0 < P.card) (hU : 0 < U.card) (hh : h ≤ U.card) (htau : 0 ≤ tau)
    (hPref : (U.card : ℝ)^h/(U.card.descFactorial h : ℝ) ≤ 2)
    (hMean : ∀ p ∈ P,∀ v : ZMod M0,
      (∑ u : U,((E p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) ≤ tau)
    (hR : ∀ p ∈ P,(p : ℝ) ≤ 2*R) (hCap : ∀ u : U,(u.val : ℝ) ≤ T) :
    sampleAverage U h (totalCost P U h M0 E) ≤ 4*R*tau^h+(M0 : ℝ)*T^h := by
  have hPnz : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  unfold totalCost
  rw [sampleAverage_div,sampleAverage_sum]
  calc
    _ ≤ (∑ p ∈ P,(2*(p : ℝ)*tau^h+(M0 : ℝ)*T^h))/(P.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun p hp =>
        primeCost_average_bound U h M0 E p tau T hU hh hPref (hMean p hp) hCap)) (Nat.cast_nonneg _)
    _ ≤ (∑ _p ∈ P,(4*R*tau^h+(M0 : ℝ)*T^h))/(P.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro p hp
      have hh := mul_le_mul_of_nonneg_right (hR p hp) (pow_nonneg htau h)
      nlinarith
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      field_simp

end ErdosInverseSampleCost

end

section

namespace ErdosInverseSampleCost
open ErdosInverseSampling ErdosInverseCRT
attribute [local instance] Classical.decEq

theorem slopes_card_le_primeCost (U : Finset ℕ) (hU : ∀ u ∈ U,u.Prime)
    (h M0 : ℕ) [NeZero M0] (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val))
    (s : Sample U h) (p q0 : ℕ) (hp : ∀ u ∈ U,p.Coprime u) (hq : ∀ u ∈ U,q0.Coprime u)
    (h0 : ∀ u ∈ U,M0.Coprime u) (a : ℕ → ℤ) (b0 : ℤ) :
    ((sourceTestedSlopes p q0 M0 (fun i => (s i).val)
      (fun i => hp _ (s i).property) (fun i => hq _ (s i).property) a b0
      (fun v i => E p v (s i))).card : ℝ) ≤ primeCost U h M0 E p s := by
  have hh := distinct_prime_sample_slope_bound U hU h s p q0 M0 hp hq h0 a b0 (fun v i => E p v (s i))
  simpa only [primeCost,Nat.cast_prod] using hh

theorem slopes_sum_le_totalCost (P U : Finset ℕ) (hU : ∀ u ∈ U,u.Prime)
    (h M0 : ℕ) [NeZero M0] (E : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val))
    (s : Sample U h) (hP : 0 < P.card) (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
    (h0 : ∀ u ∈ U,M0.Coprime u) (q0 : ℕ) (hq : ∀ u ∈ U,q0.Coprime u)
    (a : ℕ → ℤ) (b0 : ℤ) :
    (∑ p : P,((sourceTestedSlopes p.val q0 M0 (fun i => (s i).val)
      (fun i => hp p.val p.property _ (s i).property) (fun i => hq _ (s i).property) a b0
      (fun v i => E p.val v (s i))).card : ℝ)) ≤
        (P.card : ℝ)*totalCost P U h M0 E s := by
  have hPnz : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  calc
    _ ≤ ∑ p : P,primeCost U h M0 E p.val s :=
      Finset.sum_le_sum (fun p _ => slopes_card_le_primeCost U hU h M0 E s p.val q0
        (hp p.val p.property) hq h0 a b0)
    _ = ∑ p ∈ P,primeCost U h M0 E p s := Finset.sum_coe_sort P (fun p : ℕ => primeCost U h M0 E p s)
    _ = _ := by unfold totalCost;field_simp

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open NumberTheoryLean ErdosInversePrimeBin ErdosInverseFrozen ErdosInverseEuler

noncomputable def frozenPrimeMean (N : ℕ) (w : ℝ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ)
    (delta U theta : ℝ) : ℝ :=
  (∑ u ∈ primeBin U theta,((frozenExceptional N w p q b v a u delta
    (SmallSieveFinite.smallEuler ⌊w⌋₊)).card : ℝ)/(u : ℝ))/((primeBin U theta).card : ℝ)

noncomputable def meanCoefficient (C K xi delta : ℝ) : ℝ :=
  32*(4+8*Real.pi^2)*C*K*Real.exp Real.eulerMascheroniConstant/(xi*delta^2)

theorem actual_mean_envelope (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∀ xi K delta : ℝ,0 < xi → xi ≤ 1 → 0 ≤ K → 0 < delta →
      ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ (N : ℕ) (p q : ℕ) (b v : ℤ) (a : ℕ → ℕ) (U theta : ℝ),
        w ≤ U → U ≤ w^K → xi/4 ≤ theta → theta ≤ xi → w^eta ≤ (N : ℝ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        frozenPrimeMean N w p q b v a delta U theta ≤
          meanCoefficient C K xi delta*(Real.log w)^2*(1/U+9*U/(N : ℝ)) := by
  obtain ⟨C,hC,w0,_hw0,hmean⟩ := frozen_exceptional_mean eta heta
  refine ⟨C,hC,?_⟩
  intro xi K delta hxi hxi1 hK hd
  filter_upwards [eventually_ge_atTop w0,uniform_edge_bin_count xi hxi hxi1,smallEuler_log_bounds]
    with w hw hb hEuler
  refine ⟨hb.1,?_⟩
  intro N p q b v a U theta hwU hUmax htlow hthigh hN hcop
  have hwpos : 0 < w := by linarith [hb.1]
  have hUpos : 0 < U := hwpos.trans_le hwU
  have hU2 : 2 ≤ U := hb.1.trans hwU
  have htpos : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans htlow
  have ht1 : theta ≤ 1 := hthigh.trans hxi1
  have hNpos : 0 < N := by exact_mod_cast (Real.rpow_pos_of_pos hwpos eta).trans_le hN
  have hlogU : Real.log U ≤ K*Real.log w := by
    have hh := Real.log_le_log hUpos hUmax
    rwa [Real.log_rpow hwpos] at hh
  have hbin := hb.2 U theta hwU htlow hthigh
  have hprimes : ∀ u ∈ primeBin U theta,u.Prime := fun u hu => ((mem_primeBin hUpos.le htpos u).mp hu).1
  have hcapped : ∀ u ∈ primeBin U theta,u ≤ edgeFrequencyCap U :=
    edge_prime_le_cap U theta hUpos.le htpos ht1
  have hspec := hmean N (edgeFrequencyCap U) w p q b v a (primeBin U theta) delta
    hw hN hcop hprimes hcapped hbin.2 hd
  exact hspec.trans (mean_envelope N (edgeFrequencyCap U) (primeBin U theta).card hNpos
    w U K xi delta C (SmallSieveFinite.smallEuler ⌊w⌋₊) (by linarith [hb.1]) (by linarith)
    hK hxi hd hC.le hEuler.2.1 hbin.1 hEuler.2.2.2 (edgeFrequencyCap_le U (by linarith)) hlogU)

end ErdosInverseSaving

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open NumberTheoryLean ErdosInversePrimeBin ErdosInverseFrozen ErdosInverseEuler ErdosInverseTail

theorem uniform_mean_power (aStar K xi delta : ℝ) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) :
    ∀ᶠ w : ℝ in atTop,4 ≤ w ∧
      ∀ (Y p q q0 : ℕ) (Qplus U theta : ℝ) (b v : ℤ) (a : ℕ → ℕ),
        0 < p → 0 < q → (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        w ≤ U → U ≤ w^K → xi/4 ≤ theta → theta ≤ xi →
        Int.ModEq (smallModulus w : ℤ) (q : ℤ) (q0 : ℤ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q).Coprime t) →
        (∀ u ∈ primeBin U theta,
          3*aStar/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*q*u))/Real.log w) →
        frozenPrimeMean (commonParentLength Y p Qplus) w p q0 b v a delta U theta ≤ w^(-aStar/2) := by
  obtain ⟨C,hC,hmean⟩ := actual_mean_envelope (aStar/2) (by positivity)
  have hA : 0 ≤ meanCoefficient C K xi delta := by unfold meanCoefficient;positivity
  filter_upwards [hmean xi K delta hxi hxi1 hK hd,uniform_edge_bin_count xi hxi hxi1,
    log_square_absorption (37*meanCoefficient C K xi delta) (aStar/4) (by positivity) (by positivity),
    eventually_ge_atTop (4 : ℝ),(tendsto_rpow_atTop (by linarith : 0 < 3*aStar/4)).eventually_ge_atTop 4]
    with w hm hb habs hw hlarge
  refine ⟨hw,?_⟩
  intro Y p q q0 Qplus U theta b v a hp hq hqQ hQq hwU hUmax htlow hthigh hqq hcop hlog
  have hwpos : 0 < w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hUpos : 0 < U := hwpos.trans_le hwU
  have htpos : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans htlow
  have hcard := (hb.2 U theta hwU htlow hthigh).2
  have hNlower := common_length_bin_lower Y p q hp hq Qplus xi w aStar U theta hqQ hQq
    hxi.le hxi1 (by linarith) ha hwU htpos hlarge (Finset.card_pos.mp hcard) hlog
  have hrho : 0 < w^(3*aStar/4) := Real.rpow_pos_of_pos hwpos _
  have hNpos : 0 < commonParentLength Y p Qplus := by
    exact_mod_cast (div_pos (mul_pos hUpos hrho) (by norm_num : (0 : ℝ) < 4)).trans_le hNlower
  have hrhoN : w^(3*aStar/4) ≤ (commonParentLength Y p Qplus : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (hw.trans hwU) hrho.le
    nlinarith
  have hEta : w^(aStar/2) ≤ (commonParentLength Y p Qplus : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hw1 (by linarith : aStar/2 ≤ 3*aStar/4)).trans hrhoN
  have hrhoU : w^(3*aStar/4) ≤ U := by
    have hh := Real.rpow_le_rpow_of_exponent_le hw1 (show 3*aStar/4 ≤ 1 by linarith)
    have hwr : w^(3*aStar/4) ≤ w := by simpa only [Real.rpow_one] using hh
    exact hwr.trans hwU
  have hcenter : ∀ t : ℕ,t.Prime → (t : ℝ) ≤ w → (p*q0).Coprime t :=
    fun t ht htw => center_step_coprime w p q q0 t ht htw hqq (hcop t ht htw)
  have hEnv := hm.2 (commonParentLength Y p Qplus) p q0 b v a U theta hwU hUmax htlow hthigh hEta hcenter
  have hFactor := spectral_factor_bound (commonParentLength Y p Qplus) hNpos U (w^(3*aStar/4))
    hUpos hrho hrhoU hNlower
  calc
    _ ≤ meanCoefficient C K xi delta*(Real.log w)^2*(1/U+9*U/(commonParentLength Y p Qplus : ℝ)) := hEnv
    _ ≤ meanCoefficient C K xi delta*(Real.log w)^2*(37/w^(3*aStar/4)) :=
      mul_le_mul_of_nonneg_left hFactor (mul_nonneg hA (sq_nonneg _))
    _ = (37*meanCoefficient C K xi delta*(Real.log w)^2)/w^(3*aStar/4) := by ring
    _ ≤ w^(aStar/4)/w^(3*aStar/4) := div_le_div_of_nonneg_right habs hrho.le
    _ = w^(-aStar/2) := by
      rw [← Real.rpow_sub hwpos]
      congr 1
      ring

end ErdosInverseSaving

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSaving
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInversePrimeBin ErdosInverseTail

theorem source_mean_power (aStar K xi delta : ℝ) (ha : 0 < aStar) (ha1 : aStar ≤ 1)
    (hK : 0 ≤ K) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) :
    ∀ᶠ z : ℝ in atTop,4 ≤ sourceW z ∧
      ∀ (p q q0 : ℕ) (Qplus U theta : ℝ) (b v : ℤ) (a : ℕ → ℕ),
        0 < p → 0 < q → (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        sourceW z ≤ U → U ≤ (sourceW z)^K → xi/4 ≤ theta → theta ≤ xi →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q).Coprime t) →
        (∀ u ∈ primeBin U theta,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        frozenPrimeMean (commonParentLength (sourceY z) p Qplus) (sourceW z) p q0 b v a delta U theta ≤
          (sourceW z)^(-aStar/2) := by
  filter_upwards [sourceW_tendsto_atTop.eventually (uniform_mean_power aStar K xi delta ha ha1 hK hxi hxi1 hd)] with z hz
  exact ⟨hz.1,hz.2 (sourceY z)⟩

end ErdosInverseSaving

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInverseFrozen ErdosInverseTail ErdosInverseEuler ErdosInversePrimeBin
attribute [local instance] Classical.decEq

noncomputable def actualFamily (Y : ℕ) (w Qplus : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (U : Finset ℕ) (M0 : ℕ) : ℕ → ZMod M0 → ∀ u : U,Finset (ZMod u.val) :=
  fun p v u => frozenExceptional (commonParentLength Y p Qplus) w p q0 b0 (v.val : ℤ) a u.val delta
    (SmallSieveFinite.smallEuler ⌊w⌋₊)

theorem actual_family_mean_eq (Y : ℕ) (w Qplus : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta U theta : ℝ) (M0 p : ℕ) (v : ZMod M0) :
    (∑ u : primeBin U theta,((actualFamily Y w Qplus q0 b0 a delta (primeBin U theta) M0 p v u).card : ℝ)/(u.val : ℝ))/
        ((primeBin U theta).card : ℝ) =
      frozenPrimeMean (commonParentLength Y p Qplus) w p q0 b0 (v.val : ℤ) a delta U theta := by
  unfold actualFamily frozenPrimeMean
  rw [Finset.sum_coe_sort (primeBin U theta) (fun u : ℕ =>
    ((frozenExceptional (commonParentLength Y p Qplus) w p q0 b0 (v.val : ℤ) a u delta
      (SmallSieveFinite.smallEuler ⌊w⌋₊)).card : ℝ)/(u : ℝ))]

noncomputable def actualCost (Y : ℕ) (w Qplus R : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h) : ℝ := by
  letI : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  exact totalCost P U h (smallModulus w) (actualFamily Y w Qplus q0 b0 a delta U (smallModulus w)) s/R

theorem actualCost_nonneg (Y : ℕ) (w Qplus R : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h) (hR : 0 ≤ R) :
    0 ≤ actualCost Y w Qplus R q0 b0 a delta P U h s := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  unfold actualCost
  exact div_nonneg (totalCost_nonneg P U h _ _ s) hR

theorem actualCost_average_bound (Y : ℕ) (w Qplus R : ℝ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ)
    (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (tau T : ℝ) (hR0 : 0 ≤ R)
    (hP : 0 < P.card) (hU : 0 < U.card) (hh : h ≤ U.card) (htau : 0 ≤ tau)
    (hPref : (U.card : ℝ)^h/(U.card.descFactorial h : ℝ) ≤ 2)
    (hMean : ∀ p ∈ P,∀ v : ZMod (smallModulus w),
      (∑ u : U,((actualFamily Y w Qplus q0 b0 a delta U (smallModulus w) p v u).card : ℝ)/(u.val : ℝ))/(U.card : ℝ) ≤ tau)
    (hR : ∀ p ∈ P,(p : ℝ) ≤ 2*R) (hCap : ∀ u : U,(u.val : ℝ) ≤ T) :
    sampleAverage U h (actualCost Y w Qplus R q0 b0 a delta P U h) ≤
      (4*R*tau^h+(smallModulus w : ℝ)*T^h)/R := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  unfold actualCost
  rw [sampleAverage_div]
  exact div_le_div_of_nonneg_right (totalCost_average_bound P U h _ _ R tau T
    hP hU hh htau hPref hMean hR hCap) hR0

end ErdosInverseSampleCost

end

section

namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseCRT ErdosInverseEuler
attribute [local instance] Classical.decEq

theorem smallModulus_coprime_largePrime (w : ℝ) (hw : 0 ≤ w) (u : ℕ)
    (hu : u.Prime) (hwu : w < (u : ℝ)) : (smallModulus w).Coprime u := by
  unfold smallModulus IntervalBoundingSieve.cutoffProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hh := LargePrimeDeletion.mem_cutoffPrimes.mp hp
  have hpw : (p : ℝ) ≤ w := (Nat.le_floor_iff hw).mp hh.2
  apply (Nat.coprime_primes hh.1 hu).mpr
  intro he
  subst p
  linarith

theorem actual_slopes_thin (Y : ℕ) (w Qplus R L : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hw : 0 ≤ w) (hR : 0 < R) (hP : 0 < P.card) (hU : ∀ u ∈ U,u.Prime)
    (huLarge : ∀ u ∈ U,w < (u : ℝ)) (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
    (hcost : actualCost Y w Qplus R qInitial bInitial a delta P U h s ≤ 1/L^6) :
    let M0 := smallModulus w
    letI : NeZero M0 := ⟨(smallModulus_pos w).ne'⟩
    ∀ (qRef : ℕ) (bRef : ℤ) (hqRef : ∀ u ∈ U,qRef.Coprime u),
      (∑ p : P,((sourceTestedSlopes p.val qRef M0 (fun i => (s i).val)
        (fun i => hp p.val p.property _ (s i).property) (fun i => hqRef _ (s i).property)
        (fun u => (a u : ℤ)) bRef
        (fun v i => actualFamily Y w Qplus qInitial bInitial a delta U M0 p.val v (s i))).card : ℝ)) ≤
          (P.card : ℝ)*R/L^6 := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  dsimp only
  intro qRef bRef hqRef
  have h0 : ∀ u ∈ U,(smallModulus w).Coprime u :=
    fun u hu => smallModulus_coprime_largePrime w hw u (hU u hu) (huLarge u hu)
  have htot : totalCost P U h (smallModulus w)
      (actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w)) s ≤ R/L^6 := by
    have hh := (div_le_iff₀ hR).mp hcost
    calc
      _ ≤ (1/L^6)*R := hh
      _ = R/L^6 := by ring
  calc
    _ ≤ (P.card : ℝ)*totalCost P U h (smallModulus w)
        (actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w)) s :=
      slopes_sum_le_totalCost P U hU h (smallModulus w) _ s hP hp h0 qRef hqRef (fun u => (a u : ℤ)) bRef
    _ ≤ (P.card : ℝ)*(R/L^6) := mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg _)
    _ = _ := by ring

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_expected_cost (aStar K alpha xi delta beta : ℝ) (h : ℕ)
    (ha : 0 < aStar) (ha1 : aStar ≤ 1) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU Qplus : ℝ,∀ (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
      z^alpha ≤ R → sourceW z ≤ U → U ≤ (sourceW z)^K →
      xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      0 < q0 → (q0 : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q0 : ℝ) →
      (∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t) →
      (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q0*u))/Real.log (sourceW z)) →
      0 < (primeBin R thetaP).card ∧ 0 < (primeBin U thetaU).card ∧ h ≤ (primeBin U thetaU).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U thetaU).card : ℝ) ∧
      sampleAverage (primeBin U thetaU) h
        (actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a delta (primeBin R thetaP) (primeBin U thetaU) h) ≤
          (4*R*((sourceW z)^(-aStar/2))^h+(smallModulus (sourceW z) : ℝ)*(2*U)^h)/R := by
  filter_upwards [source_mean_power aStar K xi delta ha ha1 hK hxi hxi1 hd,
    source_sample_population xi beta h hxi hxi1,source_sample_population xi 1 0 hxi hxi1,
    sourceW_le_power alpha halpha,eventually_gt_atTop (1 : ℝ)] with z hmean hpop hpopP hWR hz
  refine ⟨hz,?_⟩
  intro R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hzpos : 0 < z := by linarith
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  have hWpos : 0 < sourceW z := by linarith [hmean.1]
  have hUpos : 0 < U := hWpos.trans_le hWU
  have hthetaP : 0 ≤ thetaP := (by positivity : (0 : ℝ) ≤ xi/4).trans hPlow
  have hthetaU : 0 ≤ thetaU := (by positivity : (0 : ℝ) ≤ xi/4).trans hUlow
  have hPo := hpopP R thetaP (hWR.trans hR) hPlow hPhigh
  have hUo := hpop U thetaU hWU hUlow hUhigh
  refine ⟨hPo.1,hUo.1,hUo.2.1,hUo.2.2.1,?_⟩
  apply actualCost_average_bound (sourceY z) (sourceW z) Qplus R q0 b0 a delta
    (primeBin R thetaP) (primeBin U thetaU) h ((sourceW z)^(-aStar/2)) (2*U) hRpos.le
    hPo.1 hUo.1 hUo.2.1 (Real.rpow_nonneg hWpos.le _) hUo.2.2.2
  · intro p hp v
    rw [actual_family_mean_eq]
    have hprime := ((mem_primeBin hRpos.le hthetaP p).mp hp).1
    exact hmean.2 p q0 q0 Qplus U thetaU b0 (v.val : ℤ) a hprime.pos hq0 hqQ hQq hWU hUtop
      hUlow hUhigh (Int.ModEq.refl _) (hcop p hp) (hlog p hp)
  · intro p hp
    have hh := ((mem_primeBin hRpos.le hthetaP p).mp hp).2.2
    have htheta1 := hPhigh.trans hxi1
    nlinarith
  · intro u
    have hh := ((mem_primeBin hUpos.le hthetaU u.val).mp u.property).2.2
    have htheta1 := hUhigh.trans hxi1
    nlinarith

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

theorem source_expected_cost_small (aStar K alpha xi delta beta eps : ℝ) (h : ℕ)
    (ha : 0 < aStar) (ha1 : aStar ≤ 1) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta)
    (heps : 0 < eps) (hh : 12 < aStar*(h : ℝ)/2) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU Qplus : ℝ,∀ (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
      z^alpha ≤ R → sourceW z ≤ U → U ≤ (sourceW z)^K →
      xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      0 < q0 → (q0 : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q0 : ℝ) →
      (∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t) →
      (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q0*u))/Real.log (sourceW z)) →
      0 < (primeBin R thetaP).card ∧ 0 < (primeBin U thetaU).card ∧ h ≤ (primeBin U thetaU).card ∧
      4*(h : ℝ)/beta ≤ ((primeBin U thetaU).card : ℝ) ∧
      sampleAverage (primeBin U thetaU) h
        (actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a delta (primeBin R thetaP) (primeBin U thetaU) h) ≤
          eps/(Real.log z)^6 := by
  filter_upwards [source_expected_cost aStar K alpha xi delta beta h ha ha1 hK halpha hxi hxi1 hd,
    source_cost_budget aStar K alpha eps h hK halpha heps hh] with z hexp hbudget
  refine ⟨hexp.1,?_⟩
  intro R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hv := hexp.2 R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hL : 0 < Real.log z := Real.log_pos hexp.1
  have hW : 0 ≤ sourceW z := div_nonneg hL.le (sq_nonneg _)
  have hs := hbudget.2 R U hR (hW.trans hWU) hUtop
  have hL6 : 0 < (Real.log z)^6 := pow_pos hL 6
  refine ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,?_⟩
  apply (le_div_iff₀ hL6).mpr
  calc
    _ ≤ ((4*R*((sourceW z)^(-aStar/2))^h+(smallModulus (sourceW z) : ℝ)*(2*U)^h)/R)*(Real.log z)^6 :=
      mul_le_mul_of_nonneg_right hv.2.2.2.2 hL6.le
    _ = (Real.log z)^6*(4*R*((sourceW z)^(-aStar/2))^h+
        (smallModulus (sourceW z) : ℝ)*(2*U)^h)/R := by ring
    _ ≤ eps := hs

end ErdosInverseSampleCost

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseSampleCost
open NumberTheoryLean ErdosInverseSampling ErdosInverseSaving ErdosInversePrimeBin ErdosInverseEuler ErdosInverseBoxHeight

noncomputable def sampleGamma (beta : ℝ) (h : ℕ) : ℝ := (beta/2)*(beta/4)^h

theorem sampleGamma_pos (beta : ℝ) (h : ℕ) (hb : 0 < beta) : 0 < sampleGamma beta h := by
  unfold sampleGamma
  positivity

theorem source_good_sample (aStar K alpha xi delta beta : ℝ) (h : ℕ)
    (ha : 0 < aStar) (ha1 : aStar ≤ 1) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hd : 0 < delta) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hh : 12 < aStar*(h : ℝ)/2) :
    ∀ᶠ z : ℝ in atTop,1 < z ∧ ∀ R thetaP U thetaU Qplus S : ℝ,
      ∀ (C : Finset ℕ) (q0 : ℕ) (b0 : ℤ) (a : ℕ → ℕ),
      z^alpha ≤ R → sourceW z ≤ U → U ≤ (sourceW z)^K →
      xi/4 ≤ thetaP → thetaP ≤ xi → xi/4 ≤ thetaU → thetaU ≤ xi →
      q0 ∈ C → 0 < q0 → (q0 : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q0 : ℝ) →
      (∀ p ∈ primeBin R thetaP,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q0).Coprime t) →
      (∀ p ∈ primeBin R thetaP,∀ u ∈ primeBin U thetaU,
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q0*u))/Real.log (sourceW z)) →
      let P := primeBin R thetaP
      let Uset := primeBin U thetaU
      let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
        (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) (sampleGamma beta h/32)
      beta*((P.product C).card : ℝ)*(Uset.card : ℝ) ≤ ((witnessPairs (P.product C) Uset witness).card : ℝ) →
      ∃ s : Sample Uset h,0 < P.card ∧ 0 < Uset.card ∧ 0 < h ∧
        sampleGamma beta h/2 ≤ selectedFraction (P.product C) Uset witness h s ∧
        actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a (delta/4) P Uset h s ≤ 1/(Real.log z)^6 := by
  have hg := sampleGamma_pos beta h hb
  have hpos : 0 < h := by
    by_contra hn
    have hh0 : h = 0 := by omega
    rw [hh0] at hh
    norm_num at hh
  filter_upwards [source_expected_cost_small aStar K alpha xi (delta/4) beta (sampleGamma beta h/4) h
    ha ha1 hK halpha hxi hxi1 (by positivity) (by positivity) hh] with z hz
  refine ⟨hz.1,?_⟩
  intro R thetaP U thetaU Qplus S C q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh
    hqC hq0 hqQ hQq hcop hlog
  dsimp only
  intro hdense
  have hv := hz.2 R thetaP U thetaU Qplus q0 b0 a hR hWU hUtop hPlow hPhigh hUlow hUhigh hq0 hqQ hQq hcop hlog
  have hC : 0 < C.card := Finset.card_pos.mpr ⟨q0,hqC⟩
  have hA : 0 < ((primeBin R thetaP).product C).card := by
    rw [Finset.product_eq_sprod,Finset.card_product]
    exact Nat.mul_pos hv.1 hC
  have hL : 0 < Real.log z := Real.log_pos hz.1
  have hzpos : 0 < z := by linarith [hz.1]
  have hRpos : 0 < R := (Real.rpow_pos_of_pos hzpos alpha).trans_le hR
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) (primeBin R thetaP) S R (sourceZ z) (sampleGamma beta h/32)
  let cost := actualCost (sourceY z) (sourceW z) Qplus R q0 b0 a (delta/4) (primeBin R thetaP) (primeBin U thetaU) h
  have hc : ∀ s : Sample (primeBin U thetaU) h,0 ≤ cost s :=
    fun s => actualCost_nonneg _ _ _ _ _ _ _ _ _ _ _ s hRpos.le
  have hcost : sampleAverage (primeBin U thetaU) h cost ≤
      (((beta/2)*(beta/4)^h)*(1/(Real.log z)^6)/4) := by
    calc
      _ ≤ (sampleGamma beta h/4)/(Real.log z)^6 := hv.2.2.2.2
      _ = _ := by unfold sampleGamma;ring
  obtain ⟨s,hs,hcs⟩ := exists_good_distinct_sample ((primeBin R thetaP).product C) (primeBin U thetaU)
    witness h beta (1/(Real.log z)^6) hb hb1 (by positivity) hA hv.2.1 hdense hv.2.2.2.1 cost hc hcost
  exact ⟨s,hv.1,hv.2.1,hpos,hs,hcs⟩

end ErdosInverseSampleCost

end

section

namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseCRT ErdosInverseEuler ErdosInverseHits ErdosInverseStructured
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def pointSlopes (Y : ℕ) (w Qplus : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u) (qRef : ℕ) (bRef : ℤ)
    (hqRef : ∀ u ∈ U,qRef.Coprime u) (p : ℕ) : Finset ℤ :=
  if hpP : p ∈ P then
    sourceTestedSlopes p qRef (smallModulus w) (fun i => (s i).val)
      (fun i => hp p hpP _ (s i).property) (fun i => hqRef _ (s i).property)
      (fun u => (a u : ℤ)) bRef
      (fun v i => actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w) p v (s i))
  else ∅

theorem pointSlopes_eq (Y : ℕ) (w Qplus : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u) (qRef : ℕ) (bRef : ℤ)
    (hqRef : ∀ u ∈ U,qRef.Coprime u) (p : ℕ) (hpP : p ∈ P) :
    pointSlopes Y w Qplus qInitial bInitial a delta P U h s hp qRef bRef hqRef p =
      sourceTestedSlopes p qRef (smallModulus w) (fun i => (s i).val)
        (fun i => hp p hpP _ (s i).property) (fun i => hqRef _ (s i).property)
        (fun u => (a u : ℤ)) bRef
        (fun v i => actualFamily Y w Qplus qInitial bInitial a delta U (smallModulus w) p v (s i)) := by
  simp only [pointSlopes,dite_eq_left hpP]

theorem pointSlopes_thin (Y : ℕ) (w Qplus R L : ℝ) (qInitial : ℕ) (bInitial : ℤ)
    (a : ℕ → ℕ) (delta : ℝ) (P U : Finset ℕ) (h : ℕ) (s : Sample U h)
    (hw : 0 ≤ w) (hR : 0 < R) (hP : 0 < P.card) (hU : ∀ u ∈ U,u.Prime)
    (huLarge : ∀ u ∈ U,w < (u : ℝ)) (hp : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
    (hcost : actualCost Y w Qplus R qInitial bInitial a delta P U h s ≤ 1/L^6)
    (qRef : ℕ) (bRef : ℤ) (hqRef : ∀ u ∈ U,qRef.Coprime u) :
    (∑ p ∈ P,((pointSlopes Y w Qplus qInitial bInitial a delta P U h s hp qRef bRef hqRef p).card : ℝ)) ≤
      (P.card : ℝ)*R/L^6 := by
  let : NeZero (smallModulus w) := ⟨(smallModulus_pos w).ne'⟩
  have hh := actual_slopes_thin Y w Qplus R L qInitial bInitial a delta P U h s hw hR hP hU huLarge hp hcost
    qRef bRef hqRef
  rw [← Finset.sum_coe_sort P (fun p : ℕ =>
    ((pointSlopes Y w Qplus qInitial bInitial a delta P U h s hp qRef bRef hqRef p).card : ℝ))]
  simpa only [pointSlopes,dite_eq_left (Subtype.property _)] using hh

theorem parentSlope_incidence (a : ℕ → ℕ) (T : ℕ → Finset ℤ) (p q : ℕ) [NeZero p]
    (hqp : q.Coprime p)
    (hs : (parentSlope p q hqp (a p) (cofactorHit q a) : ℤ) ∈ T p) :
    SlopeIncidence (fun u => (a u : ℤ)) T (cofactorPoint a q) p := by
  refine ⟨(parentSlope p q hqp (a p) (cofactorHit q a) : ℤ),hs,?_⟩
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (parent_start_mod_p p q hqp (a p) (cofactorHit q a))
  simp only [Nat.cast_add,Nat.cast_mul] at he
  change ((cofactorHit q a : ℤ) : ZMod p) = ((a p : ℤ) : ZMod p)-
    ((parentSlope p q hqp (a p) (cofactorHit q a) : ℤ) : ZMod p)*((q : ℤ) : ZMod p)
  simp only [Int.cast_natCast]
  linear_combination he

end ErdosInverseRefinement

end

end Erdos970

end OAI
