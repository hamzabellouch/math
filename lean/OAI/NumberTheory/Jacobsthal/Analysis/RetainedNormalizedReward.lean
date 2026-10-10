import OAI.NumberTheory.Jacobsthal.Partitions.SourceNodeCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosRetainedRewardTransfer
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.PrimeKilledChain NumberTheoryLean.PrimeCompactWeights
open NumberTheoryLean.PrimeCorrectionFactor NumberTheoryLean.PrimeFamilyOccupation
open NumberTheoryLean.SourceNodeCoordinates
open NumberTheoryLean.PrimeBinMembership
open ErdosPrimeInputs.PrimePrefixMass

noncomputable def transferConstant : ℝ := 2*weight .even (199/100)

theorem transferConstant_positive : 0 < transferConstant := by
  unfold transferConstant
  exact mul_pos (by norm_num) (weight_pos (by norm_num [Valid]))

theorem scaled_normalized_reward_bound {d w ell B delta : ℝ} {start : Node}
    (hB : 0 < B) (hell : 1 ≤ ell) (hlogB : 2 ≤ Real.log B)
    (hcomp : Real.log B ≤ d*Real.log w) (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) (_hdelta : 0 ≤ delta)
    (h : History w ell ((Real.log B)^2) start) (F : List ℕ → ℝ)
    (hF : h.node.gap^2*|F h.primes|/weight h.node.side h.node.ratio ≤ delta) :
    scaledWeight w B start (some h)*|F h.primes| ≤ transferConstant*delta := by
  obtain ⟨hs,hr,hBr,hsize⟩ := source_node_bounds hB start hi h199 h23 hcons hcut
  have hphi : 0 < weight h.node.side h.node.ratio := weight_pos (terminal_valid hs h.admissible)
  have hp0 : 0 ≤ weight start.side start.ratio := (weight_pos hs).le
  have hW : 0 ≤ weight .even (199/100) := (weight_pos (by norm_num [Valid])).le
  have hinit : weight start.side start.ratio ≤ weight .even (199/100) := by
    rw [hi]
    exact NumberTheoryLean.TwoStepDensityBounds.weight_antitone (by norm_num [Valid]) (hi ▸ hs) h199
  have hc : (1+epsilon w)^h.primes.length ≤ 2 := by
    have hh := (history_correction hlogB hcomp hell hr hs hB hsize h).2
    linarith
  have hc0 : 0 ≤ (1+epsilon w)^h.primes.length := pow_nonneg (normalizer_pos w).le _
  have hratio : 0 ≤ B/start.gap := div_nonneg hB.le hr.le
  have hratio1 : B/start.gap ≤ 1 := (div_le_one hr).mpr hBr
  have hsq : (B/start.gap)^2 ≤ 1 := by nlinarith
  have hF0 : 0 ≤ h.node.gap^2*|F h.primes|/weight h.node.side h.node.ratio := by positivity
  calc
    _ = ((B/start.gap)^2*(1+epsilon w)^h.primes.length*weight start.side start.ratio)*
        (h.node.gap^2*|F h.primes|/weight h.node.side h.node.ratio) := by unfold scaledWeight; ring
    _ ≤ (1*2*weight .even (199/100))*delta :=
      mul_le_mul (mul_le_mul (mul_le_mul hsq hc hc0 (by norm_num)) hinit hp0 (by norm_num)) hF hF0 (by positivity)
    _ = _ := by unfold transferConstant; ring

theorem retained_normalized_reward_sum {d w ell B delta : ℝ} {start : Node}
    (hw : normalizationThreshold ≤ w) (hell : 1 ≤ ell)
    (hS : (Real.log B)^2 ≤ (Real.log w)^3) (hsS : start.ratio ≤ (Real.log B)^2)
    (hB : 0 < B) (hlogB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w)
    (hbudget : correctionBudget d w ≤ 1)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hcons : Consistent start) (hcut : start.cutoff=B) (hdelta : 0 ≤ delta) (F : List ℕ → ℝ)
    (hF : ∀ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,
      (terminal w start ps).gap^2*|F ps|/weight (terminal w start ps).side (terminal w start ps).ratio ≤ delta) :
    B^2*(∑ ps ∈ retainedPrefixes w ell ((Real.log B)^2) start,prefixWeight ps*|F ps|) ≤
      transferConstant*(NumberTheoryLean.LowStateHorizon.sourceHorizon ((Real.log B)^2) B : ℝ)*delta := by
  classical
  obtain ⟨hs,hr,_hBr,hsize⟩ := source_node_bounds hB start hi h199 h23 hcons hcut
  have hw1 : 1 < w := normalizationThreshold_gt_one.trans_le hw
  let := historyFintype (ell:=ell) (S:=(Real.log B)^2) hw1 start
  have hpoint (z : ChainState w ell ((Real.log B)^2) start) :
      ‖scaledWeight w B start z*listReward (fun ps => |F ps|) z‖ ≤ transferConstant*delta := by
    cases z with
    | none =>
      simp only [scaledWeight,listReward,mul_zero,norm_zero]
      exact mul_nonneg transferConstant_positive.le hdelta
    | some h =>
      have hnorm : 0 ≤ scaledWeight w B start (some h)*|F h.primes| :=
        mul_nonneg (scaledWeight_nonneg hs _) (abs_nonneg _)
      change ‖scaledWeight w B start (some h)*|F h.primes|‖ ≤ transferConstant*delta
      rw [Real.norm_of_nonneg hnorm]
      apply scaled_normalized_reward_bound hB hell hlogB hcomp hbudget hi h199 h23 hcons hcut hdelta h F
      exact hF h.primes ((mem_retainedPrefixes hw1 start h.primes).mpr h.admissible)
  have hterm (n : ℕ) :
      (∫ z,scaledWeight w B start z*listReward (fun ps => |F ps|) z ∂pathLaw w ell ((Real.log B)^2) start n) ≤
        transferConstant*delta := by
    let := pathLaw_isProbability hw hell (sq_nonneg _) hS hr hs hsS n
    have hn := norm_integral_le_of_norm_le_const (μ:=pathLaw w ell ((Real.log B)^2) start n)
      (Filter.Eventually.of_forall hpoint)
    rw [Real.norm_eq_abs] at hn
    have hle := le_abs_self (∫ z,scaledWeight w B start z*listReward (fun ps => |F ps|) z ∂pathLaw w ell ((Real.log B)^2) start n)
    exact hle.trans (by simpa using hn)
  rw [← finite_signed_original_occupation hw hell (sq_nonneg _) hS hr hs hsS hB hsize (fun ps => |F ps|)]
  calc
    _ ≤ ∑ _n ∈ range (NumberTheoryLean.LowStateHorizon.sourceHorizon ((Real.log B)^2) B),transferConstant*delta :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end ErdosRetainedRewardTransfer

end

end Erdos970

end OAI
