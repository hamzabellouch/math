import Mathlib
import OAI.Combinatorics.UniformKServer.StarCaps
import OAI.Combinatorics.UniformKServer.StarLower
import OAI.Combinatorics.UniformKServer.StarTrackers
import OAI.Combinatorics.UniformKServer.EpochOutputParameters

namespace OAI

                                                
section

/-! Explicit room for the actual held parameters in the two output rules.
The inequalities include arbitrarily small dominant side proportions. -/
noncomputable section
namespace UniformKServer.StarFeasibilityParameters
open Finset StarRanks StarSchedules StarLower
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

def sideReference (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  SideReferenceSchedule.reference (fun s => held d s ω) (fun s => parentRefresh d δ s ω) t

theorem side_valid_reference (d : Data Ω ι k) (δ : ℝ) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d δ t ω)=some o) :
    EpochParameters.sideReference (held d t ω) o (sideReference d δ t ω) :=
  SideReferenceSchedule.reference_spec (fun s i => held_nonneg d s ω i) _ t ho

def alphaParam (d : Data Ω ι k) (t : ℕ) (ω : Ω) : AlphaEmpty.Config ι :=
  StarTrackers.alphaParam d StarConstants.delta StarConstants.ct StarConstants.multiplier t ω

def sideParam (d : Data Ω ι k) (t : ℕ) (ω : Ω) : AdaptiveSide.Config ι :=
  StarTrackers.sideParam d StarConstants.delta StarConstants.cw t ω

theorem alpha_valid (d : Data Ω ι k) (t : ℕ) (ω : Ω) : AlphaEmpty.valid (alphaParam d t ω) :=
  (StarTrackers.alphaData d StarConstants.delta StarConstants.ct_pos
    StarConstants.ct_height StarConstants.multiplier_bound).param_valid t ω

theorem side_valid (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    AdaptiveSide.valid (sideParam d t ω) :=
  (StarTrackers.sideData d hk StarConstants.delta_bounds.1 StarConstants.cw_pos
    StarConstants.cw_height).param_valid t ω

theorem regular_room_algebra {β γ η h ell : ℝ} (hl : 0 < ell) (hh : 1 ≤ h)
    (hβ : 0 ≤ β) (hβ4 : β ≤ 4) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hηb : η ≤ StarConstants.ct*h/ell)
    (hgap : (ParentBeta.cBeta/50)/ell*h ≤ γ-β) :
    (β+4*StarConstants.eps/ell)*(1+η) ≤ γ := by
  have heta := (le_div_iff₀ hl).mp hηb
  have hg : (ParentBeta.cBeta/50)*h ≤ (γ-β)*ell := by
    apply (div_le_iff₀ hl).mp
    calc
      _ = (ParentBeta.cBeta/50)/ell*h := by ring
      _ ≤ _ := hgap
  have hp := mul_le_mul_of_nonneg_left heta hβ
  have hp' := mul_le_mul_of_nonneg_right hβ4 (mul_nonneg StarConstants.ct_pos.le (by linarith : 0 ≤ h))
  have he : 4*StarConstants.eps*(1+η) ≤ 8*StarConstants.eps*h := by
    norm_num [StarConstants.eps] at *
    nlinarith only [hh,hη1]
  have hid : ((β+4*StarConstants.eps/ell)*(1+η))*ell =
      β*ell+β*(η*ell)+4*StarConstants.eps*(1+η) := by field_simp
  apply (mul_le_mul_iff_left₀ hl).mp
  rw [hid]
  norm_num [StarConstants.ct,StarConstants.eps,ParentBeta.cBeta] at hg hp hp' he ⊢
  nlinarith only [hg,hp,hp',he,hh]

theorem regular_room (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hai : 0 < held d t ω i)
    (hi : EpochGeometry.dominant (epoch d StarConstants.delta t ω) ≠ some i) :
    (parentBeta d t ω+4*StarConstants.eps/EpochAlpha.ell k)*
        (1+AlphaEmpty.eta (alphaParam d t ω) i) ≤ childBeta d t ω i := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have he := EpochOutputParameters.eta_regular hs hl StarConstants.ct_pos.le i hai hi
    (U:=sideReference d StarConstants.delta t ω) (C:=StarConstants.multiplier)
  have hp := alpha_valid d t ω
  have hηn : 0 ≤ AlphaEmpty.eta (alphaParam d t ω) i := (EpochOutputParameters.eta_range hp i).1
  have hη1 : AlphaEmpty.eta (alphaParam d t ω) i ≤ 1 := (EpochOutputParameters.eta_range hp i).2
  have hb := parent_allowed d hk t ω
  exact regular_room_algebra hl (EpochParameters.regular_height hs hai hi)
    (by linarith [hb.1]) (by linarith [hb.2]) hηn hη1 he
    (StarParameters.regular_gap d hk t ω _ hs i hai hi)

theorem dominant_room (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) :
    parentBeta d t ω*(1+AlphaEmpty.eta (alphaParam d t ω) o) ≤ childBeta d t ω o := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hU := side_valid_reference d StarConstants.delta t ω o ho
  have he := EpochOutputParameters.eta_dominant hs (sideReference d StarConstants.delta t ω)
    (EpochAlpha.ell k) StarConstants.ct StarConstants.multiplier o ho
  change AlphaEmpty.eta (alphaParam d t ω) o = _ at he
  rw [he]
  have hg := StarParameters.dominant_gap d hk t ω _ hs o ho _ hU
  change (ParentBeta.cBeta/3)/EpochAlpha.ell k*(_/_) ≤ childBeta d t ω o-parentBeta d t ω at hg
  have hb := parent_allowed d hk t ω
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have hu := div_nonneg hU.1 (EpochGeometry.dominant_spec ho).1.le
  have hc : parentBeta d t ω*StarConstants.ct ≤ ParentBeta.cBeta/3 := by
    norm_num [ParentBeta.cBeta,StarConstants.ct]
    linarith [hb.2]
  have hh := mul_le_mul_of_nonneg_right hc (div_nonneg hu hl.le)
  calc
    _ = parentBeta d t ω+(parentBeta d t ω*StarConstants.ct)*
        ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k) := by ring
    _ ≤ parentBeta d t ω+(ParentBeta.cBeta/3)*
        ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k) := by linarith only [hh]
    _ ≤ childBeta d t ω o := by
      simp only [div_eq_mul_inv] at hg ⊢
      nlinarith only [hg]

theorem side_room (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (i : ι)
    (hi : i ∈ (sideParam d t ω).active) :
    (sideParam d t ω).b+AdaptiveSide.theta (sideParam d t ω) i ≤ childBeta d t ω i := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hm := EpochSide.mem hi
  have hh := EpochParameters.regular_height hs hm.1 hm.2
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have hg := StarParameters.regular_gap d hk t ω _ hs i hm.1 hm.2
  change (ParentBeta.cBeta/50)/EpochAlpha.ell k*_ ≤ childBeta d t ω i-parentBeta d t ω at hg
  have he := EpochOutputParameters.theta_active (EpochAlpha.ell k) StarConstants.cw
    (upper d StarConstants.delta t ω) hi
  change AdaptiveSide.theta (sideParam d t ω) i = _ at he
  have hp := (ParentBeta.parameter_accuracy (parentInput d) StarConstants.delta_bounds.1 hk t ω).2
  change (sideParam d t ω).b ≤ parentBeta d t ω+_ at hp
  rw [he]
  have hconst : 4*ParentBeta.cBeta*StarConstants.delta+
      StarConstants.cw*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i) ≤
      (ParentBeta.cBeta/50)*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i) := by
    have hh' := hh
    norm_num [ParentBeta.cBeta,StarConstants.delta,StarConstants.cw] at hh' ⊢
    linarith only [hh']
  have hdiv := div_le_div_of_nonneg_right hconst hl.le
  rw [add_div] at hdiv
  calc
    _ ≤ parentBeta d t ω+(4*ParentBeta.cBeta*StarConstants.delta)/EpochAlpha.ell k+
        StarConstants.cw*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i)/EpochAlpha.ell k := by linarith only [hp]
    _ ≤ parentBeta d t ω+(ParentBeta.cBeta/50)*SideParameters.height (EpochGeometry.total (epoch d StarConstants.delta t ω).base) (held d t ω i)/EpochAlpha.ell k := by linarith only [hdiv]
    _ ≤ childBeta d t ω i := by
      simp only [div_eq_mul_inv] at hg ⊢
      nlinarith only [hg]


theorem side_slack (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) :
    deficit d StarConstants.delta t ω*(∑ i ∈ univ.erase o,
        AdaptiveSide.theta (sideParam d t ω) i*AdaptiveSide.offset (sideParam d t ω) i) ≤
      lower d (parentBeta d t ω) t ω o-lower d (childBeta d t ω o) t ω o := by
  have hs := epoch_valid d StarConstants.delta t ω
  have hU := side_valid_reference d StarConstants.delta t ω o ho
  have hl : 0 < EpochAlpha.ell k := lt_of_lt_of_le zero_lt_one (EpochAlpha.ell_one k)
  have hu := div_nonneg hU.1 (EpochGeometry.dominant_spec ho).1.le
  have hsum := EpochOutputParameters.side_sum_bound hs (held_nonneg d t ω)
    hl StarConstants.cw_pos.le (upper d StarConstants.delta t ω) o ho hU
  change (∑ i ∈ univ.erase o, AdaptiveSide.theta (sideParam d t ω) i*
    AdaptiveSide.offset (sideParam d t ω) i) ≤ _ at hsum
  have hD := (StarCaps.deficit_comparison d hk t ω o ho).2
  have hD0 := deficit_nonneg d StarConstants.delta t ω
  have hT := FlexEstimates.flex_nonneg (input d o) (parent_allowed d hk t ω) t ω
  have hK : 0 ≤ (1001/1000)*StarConstants.cw/EpochAlpha.ell k*
      (sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) StarConstants.cw_pos.le) hl.le) hu
  have hc : 2*(1001/1000)*StarConstants.cw ≤ ParentBeta.cBeta/288 := by
    norm_num [StarConstants.cw,ParentBeta.cBeta]
  have hh := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (div_nonneg hu hl.le) hT)
  calc
    _ ≤ deficit d StarConstants.delta t ω*((1001/1000)*StarConstants.cw/EpochAlpha.ell k*
        (sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)) :=
      mul_le_mul_of_nonneg_left hsum hD0
    _ ≤ (2*FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω)*
        ((1001/1000)*StarConstants.cw/EpochAlpha.ell k*
        (sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)) :=
      mul_le_mul_of_nonneg_right hD hK
    _ ≤ (ParentBeta.cBeta/288)*(sideReference d StarConstants.delta t ω/
        EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k*
        FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω := by
      calc
        _ = (2*(1001/1000)*StarConstants.cw)*
            ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k*
              FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω) := by ring
        _ ≤ (ParentBeta.cBeta/288)*
            ((sideReference d StarConstants.delta t ω/EpochGeometry.total (epoch d StarConstants.delta t ω).base)/EpochAlpha.ell k*
              FlexEstimates.trueFlex (input d o) (parentBeta d t ω) t ω) := hh
        _ = _ := by ring
    _ ≤ _ := dominant_slack d hk t ω _ hs o ho _ hU

end UniformKServer.StarFeasibilityParameters

end


end

end OAI
