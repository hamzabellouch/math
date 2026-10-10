import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CorePriceExcess

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma coreCoulombAt_continuousOn_separated {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A B : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ a ∈ A, ∀ z ∈ B, d ≤ ‖a-z‖) : ContinuousOn (coreCoulombAt ψ) B := by
  apply continuousOn_finsetSum
  intro s _
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_of_dominated (bound := fun x => ‖ψ.value s x‖^2/d)
  · intro z _
    exact (((hψ.1 s).aestronglyMeasurable.aemeasurable.norm.pow_const 2).div
      (((continuous_apply i).sub continuous_const).norm.aemeasurable)).aestronglyMeasurable
  · intro z hz
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (norm_nonneg _))]
      by_cases hi : x i ∈ A
      · exact div_le_div_of_nonneg_left (sq_nonneg _) hd (hsep _ hi _ hz)
      · simp only [(hc x i hi s).1,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,le_refl]
  · exact ((hψ.1 s).integrable_norm_pow (by decide)).div_const d
  · exact Eventually.of_forall fun x => by
      by_cases hi : x i ∈ A
      · exact continuousOn_const.div
          ((continuous_const.sub continuous_id).norm.continuousOn)
          (fun z hz => (hd.trans_le (hsep _ hi _ hz)).ne')
      · simp only [(hc x i hi s).1,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div]
        exact continuousOn_const

lemma normalizedCoreField_continuousOn_patch {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ) :
    ContinuousOn (fun x => normalizedCoreField Z lam ψ (y+x)) (closedBall 0 R) := by
  have hcore := coreCoulombAt_continuousOn_separated hψ A (closedBall y R) hc hd hsep
  have hh : ContinuousOn (normalizedCoreField Z lam ψ) (closedBall y R) :=
    ((continuousOn_const.div continuous_norm.continuousOn
      (fun z hz => (hr.trans_le (hnuc _ hz)).ne')).sub hcore |>.div_const _).sub continuousOn_const
  exact hh.comp (continuous_const.add continuous_id).continuousOn (fun x hx => by
    simpa only [mem_closedBall,dist_eq_norm,sub_zero,add_sub_cancel_left] using hx)

lemma tfBallPotential_continuous (R : ℝ) (f : TFLp (ballMeasure R)) :
    Continuous (tfBallPotential R f) := by
  have hp : MemLp (tfExtension R f) (5/3) := by
    rw [tfExtension, memLp_indicator_iff_restrict measurableSet_ball]
    exact Lp.memLp f
  have he : tfPotential (tfExtension R f) = tfBallPotential R f := funext (tfPotential_extension R f)
  rw [←he]
  exact tfPotential_continuous (tfExtension_integrable R f) hp

lemma actualPatchField_continuousOn {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (y : Space) (R : ℝ) {d r : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    (f : TFLp (ballMeasure R)) :
    ContinuousOn (fun x => normalizedCoreField Z lam ψ (y+x)-tfBallPotential R f x)
      (closedBall 0 R) :=
  (normalizedCoreField_continuousOn_patch hψ A hc y R hd hr hnuc hsep Z lam).sub
    (tfBallPotential_continuous R f).continuousOn

end CoulombAtom

end

end OAI
