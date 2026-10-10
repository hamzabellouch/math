import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailComparison
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFieldDifference
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorNonlinearTail

namespace OAI

/-! Sup-norm convergence of the actual nonlinear tail fixed points to the free one. -/

open Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_tail_fixedPoint_limit
    (κ : ℝ) (ν : ℕ → ℂ) (ν₀ m : ℂ) (δ : ℝ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hδ : 0 ≤ δ) (hsmall : ‖m‖+2*δ < 1)
    (hκ : radialExteriorMatrixBound ν₀ < κ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ n, Continuous (f n))
    (r : ℕ → ℝ →ᵇ ℂ × ℂ) (r₀ : ℝ →ᵇ ℂ × ℂ) (hr : Tendsto r atTop (nhds r₀))
    (v : ℕ → ℝ →ᵇ ℂ × ℂ) (w : ℝ →ᵇ ℂ × ℂ)
    (hv : ∀ᶠ n in atTop, ∀ t, v n t=radialExteriorTailIntegral κ
      (fun s => radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ) (f n) (r n) s (v n s)) t)
    (hw : ∀ t, w t=radialExteriorTailIntegral κ
      (fun s => radialExteriorErrorMatrix ν₀ (w s)+r₀ s) t) :
    Tendsto v atTop (nhds w) := by
  have hκpos : 0 < κ := (radialExteriorMatrixBound_pos ν₀).trans hκ
  let L : ℕ → ℝ := fun n => radialExteriorMatrixBound (ν n)+radialExteriorCutoffRate n m δ
  let E : ℕ → ℝ := fun n =>
    (radialExteriorMatrixDifference (ν n) ν₀+radialExteriorCutoffRate n m δ)*‖w‖+‖r n-r₀‖
  have hB : Tendsto (fun n => radialExteriorMatrixBound (ν n)) atTop
      (nhds (radialExteriorMatrixBound ν₀)) := by
    have hc : Continuous radialExteriorMatrixBound := by unfold radialExteriorMatrixBound; fun_prop
    exact hc.continuousAt.tendsto.comp hν
  have hD : Tendsto (fun n => radialExteriorMatrixDifference (ν n) ν₀) atTop (nhds 0) := by
    have hc : Continuous (fun z => radialExteriorMatrixDifference z ν₀) := by
      unfold radialExteriorMatrixDifference
      fun_prop
    simpa only [Function.comp_def,radialExteriorMatrixDifference,sub_self,norm_zero,add_zero] using
      hc.continuousAt.tendsto.comp hν
  have hRate := radialExteriorCutoffRate_tendsto m δ hδ hsmall
  have hL : Tendsto L atTop (nhds (radialExteriorMatrixBound ν₀)) := by
    simpa only [L,add_zero] using hB.add hRate
  have hE : Tendsto E atTop (nhds 0) := by
    simpa only [E,add_zero,zero_mul] using
      ((hD.add hRate).mul_const ‖w‖).add (tendsto_iff_norm_sub_tendsto_zero.mp hr)
  have hbound : Tendsto (fun n => E n/(κ-L n)) atTop (nhds 0) := by
    have hb := hE.div (tendsto_const_nhds.sub hL) (sub_pos.mpr hκ).ne'
    change Tendsto (fun n => E n/(κ-L n)) atTop
      (nhds (0/(κ-radialExteriorMatrixBound ν₀))) at hb
    simpa only [zero_div] using hb
  have hLevent : ∀ᶠ n in atTop, L n < κ := hL.eventually (gt_mem_nhds hκ)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hbound
  filter_upwards [hLevent,hv] with n hn hvn
  have hRate0 := radialExteriorCutoffRate_nonneg n m δ
  have hLn : 0 ≤ L n := add_nonneg (radialExteriorMatrixBound_pos (ν n)).le hRate0
  have hEn : 0 ≤ E n := by
    dsimp [E,radialExteriorMatrixDifference]
    positivity
  let N := radialExteriorErrorField κ (ν n) (radialExteriorCutoffPower n m δ) (f n) (r n)
  let M := radialExteriorErrorField κ ν₀ (fun _ => 0) (fun _ => 0) r₀
  have hM : ∀ t z, M t z=radialExteriorErrorMatrix ν₀ z+r₀ t := by
    intro t z
    simp [M,radialExteriorErrorField,radialExteriorWeightedIncrement]
  have hzeroLip : ∀ z u : ℂ, ‖(0 : ℂ)-0‖ ≤ (0 : ℝ)*‖z-u‖ := by simp
  have hcutLip := radialExteriorCutoffPower_difference n m δ hδ
  have hw' : ∀ t, w t=radialExteriorTailIntegral κ (fun s => M s (w s)) t := by
    simpa only [M,radialExteriorErrorField,radialExteriorWeightedIncrement,sub_self,mul_zero,
      Prod.mk_zero_zero,add_zero] using hw
  apply radialExterior_fixedPoint_difference κ (L n) (radialExteriorMatrixBound ν₀)
    ‖r n‖ ‖r₀‖ (E n) hκpos hLn (radialExteriorMatrixBound_pos ν₀).le hn hEn N M
    (radialExteriorErrorField_continuous κ (ν n) _ (radialExteriorCutoffPower_continuous n m δ)
      (f n) (hf n) (r n))
    (radialExteriorErrorField_continuous κ ν₀ _ continuous_const _ continuous_const r₀)
    (fun t => by simpa only [N,radialExteriorErrorField_zero] using (r n).norm_coe_le_norm t)
    (fun t => by simpa only [M,radialExteriorErrorField_zero] using r₀.norm_coe_le_norm t)
    (radialExteriorErrorField_difference κ _ hRate0 (ν n) _ hcutLip (f n) (r n))
    (by simpa only [add_zero] using
      radialExteriorErrorField_difference κ 0 (by norm_num) ν₀ _ hzeroLip (fun _ => 0) r₀)
    (v n) w hvn hw'
  intro t
  rw [hM]
  calc
    _ ≤ (radialExteriorMatrixDifference (ν n) ν₀+radialExteriorCutoffRate n m δ)*‖w t‖+
        ‖r n-r₀‖ := radialExteriorErrorField_linear_difference κ _ (ν n) ν₀ _ hcutLip (f n) (r n) r₀ t (w t)
    _ ≤ E n := by
      apply (add_le_add_iff_right ‖r n-r₀‖).mpr
      exact mul_le_mul_of_nonneg_left (w.norm_coe_le_norm t)
        (add_nonneg (by unfold radialExteriorMatrixDifference; positivity) hRate0)

end DefocusingNLS

end OAI
