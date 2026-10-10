import OAI.Geometry.RCD.Sobolev.LocalGradientLipschitz
import OAI.Geometry.RCD.Sobolev.NestedBallCutoff

namespace OAI

/-! # Bounded gradient representatives between two concentric balls

The cutoff gap, rather than the inner radius, controls the global
Lipschitz extension. This allows every strict interior fraction.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.interior_bounded_gradient_representative
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) (R T : ℝ) (hRT : R<T) (L M : ℝ≥0)
    (hM : ∀ᵐ x ∂hausdorff n X, dist p x ≤ T →
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ M)
    (hL : ∀ᵐ x ∂hausdorff n X, dist p x ≤ T →
      SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic u x ≤ L) :
    ∃ v : X → ℝ,
      LipschitzWith ⟨Real.sqrt (2*(L:ℝ)^2+2*(M:ℝ)^2*((T-R)⁻¹)^2),Real.sqrt_nonneg _⟩ v ∧
      (∀ x, |v x| ≤ M) ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[
        (hausdorff n X).restrict (ball p R)] v := by
  let := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.IsOpenPosMeasure := hX.openPos K n
  let χ := nestedBallCutoff p R T
  let hχ := nestedBallCutoff_lipschitz p hRT
  let hs := nestedBallCutoff_hasCompactSupport p hRT
  have hb (x : X) : |χ x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (nestedBallCutoff_bounds p R T x).1]
    exact (nestedBallCutoff_bounds p R T x).2
  have hnon (x : X) : 0 ≤ χ x := (nestedBallCutoff_bounds p R T x).1
  let η := SobolevSpace.ofLipschitzCompact μ hX.quadratic hχ hs
  have hη : SobolevSpace.toLp μ hX.quadratic η =ᵐ[μ] χ :=
    SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hχ hs
  let z := SobolevSpace.cutoffCLM μ hX.quadratic hχ hs hb hnon u
  have hzrep : SobolevSpace.toLp μ hX.quadratic z =ᵐ[μ]
      fun x => χ x*SobolevSpace.toLp μ hX.quadratic u x :=
    SobolevSpace.cutoffCLM_coe μ hX.quadratic hχ hs hb hnon u
  have hηG := SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic η hχ hη
  let A := 2*(L:ℝ)^2+2*(M:ℝ)^2*((T-R)⁻¹)^2
  have hzg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic z x ≤ Real.sqrt A := by
    filter_upwards [minimalSlope_cutoffCLM_sq_le μ hX.quadratic u η hχ hs hb hnon hη,
      hη,hM,hL,hηG,hzrep,SobolevSpace.minimalSlope_zero_on_level μ hX.quadratic z 0,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic u),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic η)] with
      x hsq hr hMx hLx hηx hzx hzero hgu hge
    apply Real.le_sqrt_of_sq_le
    by_cases hx : dist p x ≤ T
    · have hχsq : (SobolevSpace.toLp μ hX.quadratic η x)^2 ≤ 1 := by
        rw [hr]
        have hχb := nestedBallCutoff_bounds p R T x
        nlinarith
      have huG : (SobolevSpace.minimalSlope μ hX.quadratic u x)^2 ≤ (L:ℝ)^2 :=
        (sq_le_sq₀ hgu L.coe_nonneg).mpr (hLx hx)
      have huF : (SobolevSpace.toLp μ hX.quadratic u x)^2 ≤ (M:ℝ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (SobolevSpace.toLp μ hX.quadratic u x)) M.coe_nonneg).mpr (hMx hx)
      have heG : (SobolevSpace.minimalSlope μ hX.quadratic η x)^2 ≤ ((T-R)⁻¹)^2 :=
        (sq_le_sq₀ hge (inv_nonneg.mpr (sub_pos.mpr hRT).le)).mpr hηx
      apply hsq.trans
      change _ ≤ 2*(L:ℝ)^2+2*(M:ℝ)^2*((T-R)⁻¹)^2
      calc
        _ ≤ 2*1*(L:ℝ)^2+2*(M:ℝ)^2*((T-R)⁻¹)^2 := by gcongr
        _ = _ := by ring
    · have hχ0 : χ x = 0 := nestedBallCutoff_eq_zero p hRT (le_of_not_ge hx)
      rw [hzero (hzx.trans (by rw [hχ0,zero_mul]))]
      norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
      dsimp only [A]
      positivity
  obtain ⟨w,hw,hew⟩ := hX.lipschitz_of_bounded_gradient K n hn
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic z) ⟨Real.sqrt A,Real.sqrt_nonneg A⟩ hzg
  have hwM : ∀ᵐ x ∂μ, |w x| ≤ M := by
    filter_upwards [hzrep,hew,hM] with x hx hwx hMx
    rw [← hwx,hx,abs_mul]
    by_cases hd : dist p x ≤ T
    · calc |χ x| * |SobolevSpace.toLp μ hX.quadratic u x| ≤ 1*(M:ℝ) :=
        mul_le_mul (hb x) (hMx hd) (abs_nonneg _) (by positivity)
        _ = M := one_mul _
    · rw [show χ x=0 from nestedBallCutoff_eq_zero p hRT (le_of_not_ge hd)]
      simpa only [abs_zero,zero_mul] using M.coe_nonneg
  have he : (fun x => min |w x| (M:ℝ)) = fun x => |w x| :=
    Measure.eq_of_ae_eq (hwM.mono fun x hx => min_eq_left hx)
      (hw.continuous.abs.min continuous_const) hw.continuous.abs
  refine ⟨w,hw,fun x => min_eq_left_iff.mp (congrFun he x),?_⟩
  filter_upwards [ae_restrict_of_ae hzrep,ae_restrict_of_ae hew,
    ae_restrict_mem measurableSet_ball] with x hx hwx hball
  have hχx : χ x=1 := nestedBallCutoff_eq_one p hRT
    (by have hd : dist x p < R := hball
        simpa only [dist_comm] using hd.le)
  rw [hχx,one_mul] at hx
  exact hx.symm.trans hwx

end RegularPointCoordinates

end

end OAI
