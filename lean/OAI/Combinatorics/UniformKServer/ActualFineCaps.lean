import Mathlib
import OAI.Combinatorics.UniformKServer.FineVariation
import OAI.Combinatorics.UniformKServer.StarParameters

namespace OAI

                                     
section

/-! Fine caps of the actual persistent rank trackers. No cap feasibility
inequality is assumed; it follows from endpoint errors and the size-log gap. -/
noncomputable section
namespace UniformKServer.ActualFineCaps
open Finset RankFunctions RankData RankTracking CoarseData FlexEstimates
open scoped Classical
variable {Ω R ι : Type*} [Fintype Ω] [Fintype R] [Fintype ι] {k : ℕ}

theorem cap_nonneg (I : R → Input Ω) {β factor : ℝ} (hβ : allowed β)
    (hf : 0 ≤ factor) (ξ : ℝ) (t : ℕ) (ω : Ω) :
    0 ≤ FineVariation.cap I β ξ factor t ω := by
  apply add_nonneg
  · exact sum_nonneg fun r _ => by split_ifs <;> norm_num
  · apply mul_nonneg hf
    exact sum_nonneg fun r _ => by split_ifs <;> first | exact le_rfl | exact (term_range _ hβ _ _ _).1

theorem cap_bound (I : R → Input Ω) {β ξ factor : ℝ} (hβ : allowed β)
    (hξ : 0 < ξ) (hξ' : ξ ≤ 1/2) (hf : factor ∈ Set.Icc (0:ℝ) 2) (t : ℕ) (ω : Ω) :
    FineVariation.cap I β ξ factor t ω ≤ 120*heldSize I t ω := by
  have ht := flex_nonneg I hβ t ω
  have hn : 0 ≤ coreCount (fun r => core (I r) t ω) :=
    sum_nonneg fun r _ => by split_ifs <;> norm_num
  have he := (flex_comparison I hβ hξ t ω).2
  have he0 : 0 ≤ estimateFlex I β ξ t ω :=
    sum_nonneg fun r _ => by split_ifs <;> first | exact le_rfl | exact (term_range _ hβ _ _ _).1
  have hfac : factor*estimateFlex I β ξ t ω ≤ 3*trueFlex I β t ω := by
    have h1 := mul_le_mul_of_nonneg_right hf.2 he0
    have h2 := mul_le_mul_of_nonneg_right hξ' ht
    nlinarith only [he,h1,h2]
  cases hb : activeState I t ω with
  | none =>
    have hz := inactive_zero I t ω β hb
    have hz' : trueFlex I β t ω=0 := hz.2.2
    unfold FineVariation.cap
    rw [hz.1,CoarseBridge.held_none I t ω hb]
    linarith
  | some b =>
    have ha := (active_accuracy I t ω hb).1
    have hd := core_flex_domination (fun r => core (I r) t ω) β
      (fun r => (I r).posterior t ω) hβ (fun r => ((I r).posterior_range t ω).1)
      (fun r hr => by
        have hp := core_small (I r) t ω hr
        norm_num [pstar] at hp ⊢
        linarith)
    change coreCount (fun r => core (I r) t ω)+trueFlex I β t ω ≤ _ at hd
    unfold FineVariation.cap
    rw [CoarseBridge.held_some I t ω hb]
    linarith

theorem coarse_comparison (I : R → Input Ω) {β : ℝ} (hβ : allowed β) (t : ℕ) (ω : Ω) :
    trueFlex I β t ω/2 ≤ estimateFlex I 3 sizeTolerance t ω ∧
      estimateFlex I 3 sizeTolerance t ω ≤ 2*trueFlex I β t ω := by
  have ht := flex_nonneg I hβ t ω
  have hg := gap_bounds I hβ t ω
  have hg0 : 0 ≤ flexGap I t ω := le_trans (div_nonneg ht (by norm_num)) hg.1
  have hsmall : 0 ≤ β-3 ∧ β-3 ≤ 1/100 := by
    norm_num [allowed] at hβ
    constructor <;> linarith [hβ.1,hβ.2]
  have he := flex_affine I β 3 t ω
  have hm := mul_nonneg hsmall.1 hg0
  have hm' := mul_le_mul hsmall.2 hg.2 hg0 (by norm_num : (0:ℝ) ≤ 1/100)
  have hlo : trueFlex I β t ω ≤ trueFlex I 3 t ω := by nlinarith only [he,hm]
  have hhi : trueFlex I 3 t ω ≤ (101/100)*trueFlex I β t ω := by nlinarith only [he,hm']
  have hc := flex_comparison I (show allowed 3 by norm_num [allowed])
    (show 0 < sizeTolerance by norm_num [sizeTolerance]) t ω
  norm_num [sizeTolerance] at hc ⊢
  constructor <;> linarith [hc.1,hc.2]

theorem held_error (d : StarRanks.Data Ω ι k) (hk : 1 ≤ k) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (t : ℕ) (ω : Ω) (i : ι) :
    |estimateFlex (StarRanks.input d i) (ParentBeta.heldParam (StarRanks.parentInput d) δ k t ω)
      (ρ/EpochAlpha.ell k) t ω-
      trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.parentInput d) k t ω) t ω| ≤
      ((ρ+4*ParentBeta.cBeta*δ)/EpochAlpha.ell k)*
      trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.parentInput d) k t ω) t ω := by
  have hb := ParentBeta.true_allowed (StarRanks.parentInput d) hk t ω (StarRanks.parent_size_bound d t ω)
  have hh := ParentBeta.held_allowed (StarRanks.parentInput d) hδ hk t ω (StarRanks.parent_size_bound d t ω)
  have hp := ParentBeta.parameter_accuracy (StarRanks.parentInput d) hδ hk t ω
  have hell : 0 < EpochAlpha.ell k := lt_of_lt_of_le (by norm_num) (EpochAlpha.ell_one k)
  have he := parameter_error (StarRanks.input d i) hb hh (div_pos hρ hell) hp.1 hp.2 t ω
  convert he using 1
  ring

theorem regular_comparison (d : StarRanks.Data Ω ι k) (hk : 1 ≤ k) {δ ρ lam ε : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hlam : 0 ≤ lam) (hlam' : lam ≤ 1/4)
    (he : ρ+4*ParentBeta.cBeta*δ ≤ lam/4)
    (hlg : 4*lam ≤ (ParentBeta.cBeta/50)/96) (hle : 4*lam ≤ ε)
    (t : ℕ) (ω : Ω) (s : EpochGeometry.State ι) (hs : EpochGeometry.valid (StarRanks.held d t ω) s)
    (i : ι) (ha : 0 < StarRanks.held d t ω i) (hi : EpochGeometry.dominant s ≠ some i) :
    trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.input d i) k t ω) t ω ≤
      (1-lam/EpochAlpha.ell k)*estimateFlex (StarRanks.input d i)
        (ParentBeta.heldParam (StarRanks.parentInput d) δ k t ω) (ρ/EpochAlpha.ell k) t ω ∧
      (1-lam/EpochAlpha.ell k)*estimateFlex (StarRanks.input d i)
        (ParentBeta.heldParam (StarRanks.parentInput d) δ k t ω) (ρ/EpochAlpha.ell k) t ω ≤
      trueFlex (StarRanks.input d i) (ParentBeta.trueParam (StarRanks.parentInput d) k t ω) t ω := by
  have hb := ParentBeta.true_allowed (StarRanks.parentInput d) hk t ω (StarRanks.parent_size_bound d t ω)
  have hell : 0 < EpochAlpha.ell k := lt_of_lt_of_le (by norm_num) (EpochAlpha.ell_one k)
  have hg := StarParameters.regular_gap d hk t ω s hs i ha hi
  have hg0 : 0 ≤ (ParentBeta.cBeta/50)/EpochAlpha.ell k := by
    exact div_nonneg (by norm_num [ParentBeta.cBeta]) hell.le
  have hheight := EpochParameters.regular_height hs ha hi
  have hgap : (ParentBeta.cBeta/50)/EpochAlpha.ell k ≤
      ParentBeta.trueParam (StarRanks.input d i) k t ω-ParentBeta.trueParam (StarRanks.parentInput d) k t ω :=
    le_trans (by simpa using mul_le_mul_of_nonneg_left hheight hg0) hg
  have hf := child_slack (StarRanks.input d i) hb hgap
    (show 0 ≤ ParentBeta.cBeta/50 by norm_num [ParentBeta.cBeta]) hell t ω
  have he0 : 0 ≤ ρ+4*ParentBeta.cBeta*δ := by
    have hcb : 0 ≤ 4*ParentBeta.cBeta := by norm_num [ParentBeta.cBeta]
    exact add_nonneg hρ.le (mul_nonneg hcb hδ.le)
  exact (FineCaps.caps (EpochAlpha.ell_one k) hlam hlam' he0 he hlg hle
    (flex_nonneg _ hb t ω) (held_error d hk hδ hρ t ω i) hf).1

end UniformKServer.ActualFineCaps

end


end

end OAI
