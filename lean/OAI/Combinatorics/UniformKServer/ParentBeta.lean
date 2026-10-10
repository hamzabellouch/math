import Mathlib
import OAI.Combinatorics.UniformKServer.ParentScale
import OAI.Combinatorics.UniformKServer.EpochAlpha

namespace OAI

                                 
section

/-! A concrete admissible absolute logarithmic coefficient and the parent's
held upper parameter. The source permits any sufficiently small positive
absolute coefficient; this choice preserves its parameter formula. -/
noncomputable section
namespace UniformKServer.ParentBeta
open Finset RankData RankTracking CoarseData ParentScale
variable {Ω R : Type*} [Fintype Ω] [Fintype R]

def cBeta : ℝ := 1/2000000

def param (k : ℕ) (X : ℝ) : ℝ := 3+cBeta/EpochAlpha.ell k*Real.log ((k:ℝ)/X)

def trueParam (I : R → Input Ω) (k t : ℕ) (ω : Ω) : ℝ := param k (trueX I t ω)

def heldParam (I : R → Input Ω) (δ : ℝ) (k t : ℕ) (ω : Ω) : ℝ := param k (lowerX I δ t ω)

theorem param_allowed {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hc : cutoff ≤ X) (hX : X ≤ k) :
    RankFunctions.allowed (param k X) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num [cutoff]) hc
  have hl := EpochAlpha.ell_one k
  have hl0 : 0 < EpochAlpha.ell k := by linarith
  have hlog0 : 0 ≤ Real.log ((k:ℝ)/X) := Real.log_nonneg ((le_div_iff₀ hX0).mpr (by simpa))
  have hrat : (k:ℝ)/X ≤ ((k:ℝ)+1)*10000 := by
    apply (div_le_iff₀ hX0).mpr
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ ((k:ℝ)+1)*10000 by positivity)
    norm_num [cutoff] at hh
    nlinarith
  have hlog := Real.log_le_log (div_pos hk0 hX0) hrat
  rw [Real.log_mul (by positivity : (k:ℝ)+1 ≠ 0) (by norm_num : (10000:ℝ) ≠ 0)] at hlog
  have hconst := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<10000)
  have hlogBound : Real.log ((k:ℝ)/X) ≤ 10000*EpochAlpha.ell k := by
    unfold EpochAlpha.ell at *
    linarith
  have hupper : cBeta/EpochAlpha.ell k*Real.log ((k:ℝ)/X) ≤ 1/200 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hl0).mpr
    norm_num [cBeta]
    nlinarith only [hlogBound]
  have hlower := mul_nonneg (div_nonneg (show 0 ≤ cBeta by norm_num [cBeta]) hl0.le) hlog0
  constructor
  · unfold param
    linarith only [hlower]
  · unfold param
    linarith only [hupper]

theorem true_allowed (I : R → Input Ω) {k : ℕ} (hk : 1 ≤ k) (t : ℕ) (ω : Ω)
    (hM : totalSize (fun r => (I r).posterior t ω) ≤ k) :
    RankFunctions.allowed (trueParam I k t ω) := by
  apply param_allowed hk (le_max_right _ _)
  apply max_le hM
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  norm_num [cutoff]
  linarith

theorem held_allowed (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k)
    (t : ℕ) (ω : Ω) (hM : totalSize (fun r => (I r).posterior t ω) ≤ k) :
    RankFunctions.allowed (heldParam I δ k t ω) := by
  have hb := lower_bounds I hδ t ω
  apply param_allowed hk hb.1
  apply hb.2.1.trans
  apply max_le hM
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  norm_num [cutoff]
  linarith

theorem parameter_accuracy (I : R → Input Ω) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (hk : 1 ≤ k)
    (t : ℕ) (ω : Ω) :
    trueParam I k t ω ≤ heldParam I δ k t ω ∧
      heldParam I δ k t ω ≤ trueParam I k t ω+(4*cBeta*δ)/EpochAlpha.ell k := by
  have hx := true_positive I t ω
  have hy := lower_positive I δ t ω
  have hb := lower_bounds I hδ t ω
  have hk0 : (0:ℝ)<k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hell : 0 < EpochAlpha.ell k := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (EpochAlpha.ell_one k)
  have hcoeff : 0 ≤ cBeta/EpochAlpha.ell k := div_nonneg (by norm_num [cBeta]) hell.le
  have he : heldParam I δ k t ω-trueParam I k t ω =
      cBeta/EpochAlpha.ell k*Real.log (trueX I t ω/lowerX I δ t ω) := by
    unfold heldParam trueParam param
    rw [Real.log_div hk0.ne' hy.ne',Real.log_div hk0.ne' hx.ne',Real.log_div hx.ne' hy.ne']
    ring
  have hlo : 0 ≤ Real.log (trueX I t ω/lowerX I δ t ω) :=
    Real.log_nonneg ((le_div_iff₀ hy).mpr (by simpa using hb.2.1))
  have hratio : trueX I t ω/lowerX I δ t ω ≤ (1+δ)^4 :=
    (div_le_iff₀ hy).mpr (by nlinarith only [hb.2.2])
  have hlog := Real.log_le_log (div_pos hx hy) hratio
  rw [Real.log_pow] at hlog
  have hlogsmall := Real.log_le_sub_one_of_pos (show 0 < 1+δ by linarith)
  have hhi : Real.log (trueX I t ω/lowerX I δ t ω) ≤ 4*δ := by norm_num at hlog; linarith
  have ha := mul_nonneg hcoeff hlo
  have hz := mul_le_mul_of_nonneg_left hhi hcoeff
  constructor
  · linarith only [he,ha]
  · have hid : cBeta/EpochAlpha.ell k*(4*δ)=(4*cBeta*δ)/EpochAlpha.ell k := by ring
    rw [hid] at hz
    linarith only [he,hz]

end UniformKServer.ParentBeta

end


end

end OAI
