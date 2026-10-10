import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombTestCharge
import OAI.Analysis.CoulombIonization.ThomasFermi.CompactDirichletBound
import OAI.Analysis.CoulombIonization.Localization.LipschitzMollifier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal Topology

namespace CoulombAnalysis

lemma tfSpace_closedBall_real (r : ℝ) (hr : 0 ≤ r) :
    volume.real (closedBall (0 : TFSpace) r) = r^3*(Real.pi*4/3) := by
  rw [Measure.real,EuclideanSpace.volume_closedBall_fin_three,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal (by positivity)]

theorem tfCoulomb_lipschitz_duality {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    (f : TFLp (ballMeasure R)) {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : Function.support g ⊆ closedBall 0 r) :
    (∫ x, g x*f x ∂ballMeasure R)^2 ≤
      (8*r^3*(L:ℝ)^2)*tfCoulombL R f f := by
  have hcg : HasCompactSupport g :=
    (isCompact_closedBall (0 : TFSpace) r).of_isClosed_subset isClosed_closure
      (closure_minimal hs isClosed_closedBall)
  let ε : ℕ → ℝ := fun n => r/((n:ℝ)+1)
  have he (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heb (n : ℕ) : ε n ≤ r := by
    dsimp [ε]
    exact div_le_self hr.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have helim : Tendsto ε atTop (𝓝 0) := by
    have hh := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
    simpa only [mul_one_div,mul_zero] using hh
  have hlim := packetSmooth_pair_tendsto (ballMeasure R)
    ((Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)) he heb helim hg hcg
  apply le_of_tendsto (hlim.pow 2)
  apply Eventually.of_forall
  intro n
  have hgn : ContDiff ℝ 2 (packetSmooth (ε n) g) :=
    (packetSmooth_contDiff (he n) hg.continuous).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hcgn := packetSmooth_compact (he n) hcg
  have hsn : tsupport (packetSmooth (ε n) g) ⊆ closedBall 0 (2*r) :=
    (packetSmooth_support (he n) hs).trans (closedBall_subset_closedBall (by linarith [heb n]))
  have hder := compact_dirichlet_bound (hgn.of_le (by norm_num)) hcgn
    (packetSmooth_lipschitz (he n) hg) hsn
  have hh := tfCoulomb_dirichlet_duality R f hgn hcgn (hsn.trans (closedBall_subset_ball hR))
  have hn : 0 ≤ (4*Real.pi)⁻¹ := by positivity
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hder hn) (tfCoulombL_nonneg R f)
  apply hh.trans
  convert hl using 1
  rw [tfSpace_closedBall_real (2*r) (by positivity)]
  field_simp [Real.pi_ne_zero]
  ring

theorem tfPatchGap_lipschitz_control {R r : ℝ} (hr : 0 < r) (hR : 2*r < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {g : TFSpace → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall 0 r) :
    (∫ x, g x*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (16*r^3*(L:ℝ)^2)*tfPatchGap R T hT Φ σ := by
  have hh := tfCoulomb_lipschitz_duality hr hR (σ-tfPatchMinimizer R T hT Φ) hg hs
  have hb := mul_le_mul_of_nonneg_left (tfPatchGap_coulomb_le R T hT Φ hσ)
    (show 0 ≤ 8*r^3*(L:ℝ)^2 by positivity)
  exact hh.trans (by nlinarith)

end CoulombAnalysis

end

end OAI
