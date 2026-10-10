import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialAxis
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchCoulombControl
import OAI.Analysis.CoulombIonization.ThomasFermi.RadialShellPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma exists_patch_density (R : ℝ) {ρ : TFSpace → ℝ} (hp : MemLp ρ (5/3))
    (hs : Function.support ρ ⊆ ball 0 R) :
    ∃ q : TFLp (ballMeasure R),
      (∀ᵐ x ∂ballMeasure R, q x = ρ x) ∧
      (∀ x, tfBallPotential R q x = tfPotential ρ x) := by
  have hm : MemLp ρ (5/3) (ballMeasure R) := hp.mono_measure Measure.restrict_le_self
  let q : TFLp (ballMeasure R) := hm.toLp ρ
  have hq : (fun x => q x) =ᵐ[ballMeasure R] ρ := hm.coeFn_toLp
  refine ⟨q,hq,fun x => ?_⟩
  change (∫ y, q y/‖x-y‖ ∂ballMeasure R) = ∫ y, ρ y/‖x-y‖
  rw [integral_congr_ae (hq.mono fun y hy => congrArg (fun z : ℝ => z/‖x-y‖) hy)]
  rw [ballMeasure,← integral_indicator measurableSet_ball]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ ball (0 : TFSpace) R
  · simp [hy]
  · have hz : ρ y = 0 := Function.notMem_support.mp (fun hh => hy (hs hh))
    simp [hy,hz]

lemma tfCoulomb_density_bound (R : ℝ) {ρ : TFSpace → ℝ}
    (hp : MemLp ρ (5/3)) (hs : Function.support ρ ⊆ ball 0 R)
    (hn : ∀ x, 0 ≤ ρ x) (hmass : ∫ x, ρ x = 1) {C : ℝ}
    (hbound : ∀ x, tfPotential ρ x ≤ C) (f : TFLp (ballMeasure R)) :
    (∫ x, tfPotential ρ x*f x ∂ballMeasure R)^2 ≤ C*tfCoulombL R f f := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density R hp hs
  have hmassq : (∫ x, q x ∂ballMeasure R) = 1 := by
    rw [integral_congr_ae hq,ballMeasure,← integral_indicator measurableSet_ball]
    convert hmass using 1
    congr 1
    funext x
    by_cases hx : x ∈ ball (0 : TFSpace) R
    · simp [hx]
    · have hz : ρ x = 0 := Function.notMem_support.mp (fun hh => hx (hs hh))
      simp [hx,hz]
  have hself : tfCoulombL R q q ≤ C := by
    rw [tfCoulombL_potential,← mul_one C,← hmassq,← integral_const_mul]
    apply integral_mono_ae (tfBallPotential_mul_integrable R q q)
      (((Lp.memLp q).integrable (Fact.out : (1:ENNReal) ≤ 5/3)).const_mul C)
    filter_upwards [hq] with x hx
    rw [hpot x,hx]
    exact mul_le_mul_of_nonneg_right (hbound x) (hn x)
  have hpair : tfCoulombL R q f = ∫ x, tfPotential ρ x*f x ∂ballMeasure R := by
    rw [tfCoulombL_potential]
    simp_rw [hpot]
  rw [← hpair]
  exact (tfCoulombL_pair_sq_le R q f).trans
    (mul_le_mul_of_nonneg_right hself (tfCoulombL_nonneg R f))

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma shell_coulomb_test_bound {R : ℝ} (f : TFLp (ballMeasure R)) (p : Space)
    {r : ℝ} (hr : 0 < r) (hpr : r < ‖p‖) (hR : ‖p‖+r < R) :
    (∫ x, tfPotential (averagedPacket p r) x*f x ∂ballMeasure R)^2 ≤
      (1/(‖p‖-r))*tfCoulombL R f f := by
  apply tfCoulomb_density_bound R (averagedPacket_memLp p hr) _
    (averagedPacket_nonneg p r) (averagedPacket_mass p hr)
  · intro x
    exact (averagedPacket_potential_bounds p hr hpr x).2.trans
      (one_div_le_one_div_of_le (by linarith) (le_max_right _ _))
  · intro x hx
    exact mem_ball_zero_iff.mpr ((averagedPacket_support p hr hx).trans_lt hR)

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAtom
open CoulombAnalysis

lemma shell_potential_tendsto (p : Space) (hp : 0 < ‖p‖) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hpr : ∀ n, r n < ‖p‖)
    (hlim : Tendsto r atTop (𝓝 0)) (x : Space) :
    Tendsto (fun n => tfPotential (averagedPacket p (r n)) x) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
  have hmax : max ‖x‖ ‖p‖ ≠ 0 := (hp.trans_le (le_max_right _ _)).ne'
  have hplus : Tendsto (fun n => 1/max ‖x‖ (‖p‖+r n)) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
    convert! tendsto_const_nhds.div
      (tendsto_const_nhds.max (tendsto_const_nhds.add hlim)) (by simpa only [add_zero] using hmax) using 1; simp
  have hminus : Tendsto (fun n => 1/max ‖x‖ (‖p‖-r n)) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
    convert! tendsto_const_nhds.div
      (tendsto_const_nhds.max (tendsto_const_nhds.sub hlim)) (by simpa only [sub_zero] using hmax) using 1; simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hplus hminus
    (fun n => (averagedPacket_potential_bounds p (hr n) (hpr n) x).1)
    (fun n => (averagedPacket_potential_bounds p (hr n) (hpr n) x).2)

lemma shell_potential_pair_tendsto (μ : Measure Space) {f : Space → ℝ}
    (hf : Integrable f μ) (p : Space) (hp : 0 < ‖p‖) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hpr : ∀ n, r n ≤ ‖p‖/2)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, tfPotential (averagedPacket p (r n)) x*f x ∂μ) atTop
      (𝓝 (∫ x, (1/max ‖x‖ ‖p‖)*f x ∂μ)) := by
  have hpr' (n : ℕ) : r n < ‖p‖ := by linarith [hpr n]
  apply tendsto_integral_of_dominated_convergence (fun x => (2/‖p‖)*‖f x‖)
  · intro n
    exact ((tfPotential_continuous (averagedPacket_integrable p (hr n))
      (averagedPacket_memLp p (hr n))).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · exact hf.norm.const_mul _
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul,Real.norm_eq_abs]
    have hh := averagedPacket_potential_bounds p (hr n) (hpr' n) x
    have hn : 0 ≤ tfPotential (averagedPacket p (r n)) x :=
      (by positivity : 0 ≤ 1/max ‖x‖ (‖p‖+r n)).trans hh.1
    rw [abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hden : ‖p‖/2 ≤ max ‖x‖ (‖p‖-r n) :=
      (by linarith [hpr n] : ‖p‖/2 ≤ ‖p‖-r n).trans (le_max_right _ _)
    have hh' := one_div_le_one_div_of_le (by positivity : 0 < ‖p‖/2) hden
    exact hh.2.trans (by convert hh' using 1; ring)
  · exact Eventually.of_forall fun x =>
      (shell_potential_tendsto p hp hr hpr' hlim x).mul_const (f x)

end CoulombAtom
namespace CoulombAnalysis
open CoulombAtom

theorem tfCoulomb_truncated_duality {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (f : TFLp (ballMeasure R)) :
    (∫ x, (1/max ‖x‖ t)*f x ∂ballMeasure R)^2 ≤ (1/t)*tfCoulombL R f f := by
  let p : Space := t • radialAxis
  have hp : ‖p‖ = t := by simp [p,norm_smul,abs_of_pos ht]
  let δ : ℝ := min (t/2) ((R-t)/2)
  have hd : 0 < δ := by dsimp [δ]; positivity
  let r : ℕ → ℝ := fun n => δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrd (n : ℕ) : r n ≤ δ := by
    exact div_le_self hd.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hrt (n : ℕ) : r n ≤ t/2 := (hrd n).trans (min_le_left _ _)
  have hrR (n : ℕ) : ‖p‖+r n < R := by
    have hh := (hrd n).trans (min_le_right (t/2) ((R-t)/2))
    rw [hp]
    linarith
  have hpr (n : ℕ) : r n < ‖p‖ := by rw [hp]; linarith [hrt n]
  have hlim : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hpair := shell_potential_pair_tendsto (ballMeasure R)
    ((Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)) p (by rwa [hp]) hr
    (fun n => by simpa only [hp] using hrt n) hlim
  rw [hp] at hpair
  have hcoef : Tendsto (fun n => (1/(‖p‖-r n))*tfCoulombL R f f) atTop
      (𝓝 ((1/t)*tfCoulombL R f f)) := by
    convert! (tendsto_const_nhds.div
      (tendsto_const_nhds.sub hlim) (show ‖p‖-0 ≠ 0 by rw [sub_zero,hp]; exact ht.ne')).mul_const
      (tfCoulombL R f f) using 1; simp only [hp,sub_zero]
  exact le_of_tendsto_of_tendsto (hpair.pow 2) hcoef
    (Eventually.of_forall fun n => shell_coulomb_test_bound f p (hr n) (hpr n) (hrR n))

theorem tfPatchGap_truncated_control {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    (∫ x, (1/max ‖x‖ t)*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (2/t)*tfPatchGap R T hT Φ σ := by
  have hh := tfCoulomb_truncated_duality ht htR (σ-tfPatchMinimizer R T hT Φ)
  have he := mul_le_mul_of_nonneg_left (tfPatchGap_coulomb_le R T hT Φ hσ)
    (by positivity : 0 ≤ 1/t)
  exact hh.trans (by convert he using 1; ring)

end CoulombAnalysis

end

end OAI
