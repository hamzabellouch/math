import OAI.Geometry.RCD.Sobolev.BoundedGradientLipschitz
import OAI.Geometry.RCD.Sobolev.CutoffPointwiseGradient

namespace OAI

/-! # A local Lipschitz estimate from weak-gradient and amplitude bounds -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A radial cutoff reduces local gradient control to the proved global
Sobolev-to-Lipschitz implication. -/
theorem NoncollapsedRCD.local_lipschitz_of_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∀ (u : SobolevSpace μ hX.quadratic) (v : X → ℝ), Continuous v →
      (SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] v) →
      ∀ (p : X) (R : ℝ), 0 < R → ∀ (L M : ℝ≥0),
      (∀ x, dist p x ≤ 2*R → |v x| ≤ M) →
      (∀ᵐ x ∂μ, dist p x ≤ 2*R → SobolevSpace.minimalSlope μ hX.quadratic u x ≤ L) →
      ∀ y, dist p y ≤ R →
        |v p-v y| ≤ Real.sqrt (2*(L:ℝ)^2+2*(M:ℝ)^2*(R⁻¹)^2)*dist p y := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.IsOpenPosMeasure := hX.openPos K n
  dsimp only
  intro u v hv hu p R hR L M hM hL y hy
  let χ := radialCutoff p R
  let hχ := radialCutoff_lipschitz p hR
  let hs := radialCutoff_hasCompactSupport p hR
  have hb (x : X) : |χ x| ≤ (1:ℝ≥0) := by
    rw [abs_of_nonneg (radialCutoff_bounds p R x).1]
    exact (radialCutoff_bounds p R x).2
  have hnon (x : X) : 0 ≤ χ x := (radialCutoff_bounds p R x).1
  let η := SobolevSpace.ofLipschitzCompact μ hX.quadratic hχ hs
  have hη : SobolevSpace.toLp μ hX.quadratic η =ᵐ[μ] χ :=
    SobolevSpace.ofLipschitzCompact_coe μ hX.quadratic hχ hs
  let z := SobolevSpace.cutoffCLM μ hX.quadratic hχ hs hb hnon u
  have hzrep : SobolevSpace.toLp μ hX.quadratic z =ᵐ[μ] fun x => χ x*v x := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hX.quadratic hχ hs hb hnon u,hu] with x hz hu
    exact hz.trans (by rw [hu])
  have hηG := SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic η hχ hη
  let A := 2*(L:ℝ)^2+2*(M:ℝ)^2*(R⁻¹)^2
  have hzg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic z x ≤ Real.sqrt A := by
    filter_upwards [minimalSlope_cutoffCLM_sq_le μ hX.quadratic u η hχ hs hb hnon hη,
      hη,hu,hL,hηG,hzrep,SobolevSpace.minimalSlope_zero_on_level μ hX.quadratic z 0,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic u),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic η)] with
      x hsq hr hux hLx hηx hzx hzero hgu hge
    apply Real.le_sqrt_of_sq_le
    by_cases hx : dist p x ≤ 2*R
    · have hχsq : (SobolevSpace.toLp μ hX.quadratic η x)^2 ≤ 1 := by
        rw [hr]
        have hχb := radialCutoff_bounds p R x
        nlinarith
      have huG : (SobolevSpace.minimalSlope μ hX.quadratic u x)^2 ≤ (L:ℝ)^2 :=
        (sq_le_sq₀ hgu L.coe_nonneg).mpr (hLx hx)
      have huF : (SobolevSpace.toLp μ hX.quadratic u x)^2 ≤ (M:ℝ)^2 := by
        rw [hux]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v x)) M.coe_nonneg).mpr (hM x hx)
      have heG : (SobolevSpace.minimalSlope μ hX.quadratic η x)^2 ≤ (R⁻¹)^2 :=
        (sq_le_sq₀ hge (inv_nonneg.mpr hR.le)).mpr hηx
      apply hsq.trans
      change _ ≤ 2*(L:ℝ)^2+2*(M:ℝ)^2*(R⁻¹)^2
      calc
        _ ≤ 2*1*(L:ℝ)^2+2*(M:ℝ)^2*(R⁻¹)^2 := by gcongr
        _ = _ := by ring
    · have hχ0 : χ x = 0 := radialCutoff_eq_zero p hR (le_of_not_ge hx)
      rw [hzero (hzx.trans (by rw [hχ0,zero_mul]))]
      norm_num only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
      dsimp only [A]
      positivity
  obtain ⟨w,hw,hew⟩ := hX.lipschitz_of_bounded_gradient K n hn
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic z) ⟨Real.sqrt A,Real.sqrt_nonneg A⟩ hzg
  have hew' : (fun x => χ x*v x) = w :=
    MeasureTheory.Measure.eq_of_ae_eq (hzrep.symm.trans hew) (hχ.continuous.mul hv) hw.continuous
  have hp : w p = v p := by
    rw [← hew']
    simp only [χ,radialCutoff_eq_one p hR (by simpa using hR.le : dist p p ≤ R),one_mul]
  have hyp : w y = v y := by
    rw [← hew']
    change χ y*v y = v y
    rw [show χ y = 1 from radialCutoff_eq_one p hR hy,one_mul]
  have hd := hw.dist_le_mul p y
  simpa only [Real.dist_eq,hp,hyp,NNReal.coe_mk,A] using! hd

end RegularPointCoordinates

end

end OAI
