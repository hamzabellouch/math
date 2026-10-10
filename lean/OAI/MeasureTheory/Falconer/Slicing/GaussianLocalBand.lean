import OAI.MeasureTheory.Falconer.Slicing.GaussianSlabBox
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

noncomputable def gaussianLocalBandConstant (n : ℕ) (ρ : ℝ) : ℝ :=
  gaussianVolumeNormalization (n+1)*
    Real.exp (-(1/2:ℝ)*(1+(n+1:ℝ)*(2*ρ))^2)*2*(2*ρ)^n

theorem gaussianLocalBandConstant_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianLocalBandConstant n ρ := by
  unfold gaussianLocalBandConstant gaussianVolumeNormalization
  positivity

theorem gaussian_local_band_lower {w b : Space (n+1)}
    (hw : ‖w‖ = 1) (hb : ‖b‖ ≤ 1) {r ρ : ℝ}
    (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwb : |inner ℝ w b| ≤ ρ) :
    ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) ≤
      stdGaussian (Space (n+1))
        {x | ‖x-b‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r} := by
  let u : Space (n+1) := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let e : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have he : e u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let c := e.symm b
  have hc : |c 0| ≤ ρ := by
    have hi : c 0 = inner ℝ w b := by
      rw [← he,← e.apply_symm_apply b,e.inner_map_map]
      exact (EuclideanSpace.basisFun_inner (Fin (n+1)) ℝ _ 0).symm
    rwa [hi]
  have hn (x : Space (n+1)) (hx : x ∈ coordinateSlabBox c r ρ) :
      ‖x‖ ≤ 1+(n+1:ℝ)*(2*ρ) := by
    calc
      _ ≤ ‖x-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (x-c) c
      _ ≤ (n+1:ℝ)*(2*ρ)+1 := add_le_add (coordinateSlabBox_distance c hrρ hc hx)
        (by simpa only [c,e.symm.norm_map] using hb)
      _ = _ := by ring
  have hl := gaussian_lower_volume_bounded (coordinateSlabBox c r ρ)
    (coordinateSlabBox_measurable c r ρ) (by positivity) hn
  rw [coordinateSlabBox_volume c hr hρ,← ENNReal.ofReal_mul
    (by unfold gaussianVolumeNormalization; positivity)] at hl
  have hl' : ENNReal.ofReal (gaussianLocalBandConstant n ρ*r) ≤
      stdGaussian (Space (n+1)) (coordinateSlabBox c r ρ) := by
    convert hl using 1
    unfold gaussianLocalBandConstant
    congr 1
    ring
  let T : Set (Space (n+1)) :=
    {x | ‖x-b‖ ≤ (n+1:ℝ)*(2*ρ) ∧ |inner ℝ w x| ≤ r}
  have hT : MeasurableSet T := by
    simp only [T,ofPred_and]
    apply MeasurableSet.inter
    · exact measurableSet_le (by fun_prop) measurable_const
    · exact measurableSet_le (by fun_prop) measurable_const
  have hs : coordinateSlabBox c r ρ ⊆ e ⁻¹' T := by
    intro x hx
    constructor
    · rw [← e.apply_symm_apply b,← e.map_sub,e.norm_map]
      exact coordinateSlabBox_distance c hrρ hc hx
    · rw [← he,e.inner_map_map]
      simpa only [u,EuclideanSpace.basisFun_inner] using hx.1
  calc
    _ ≤ stdGaussian (Space (n+1)) (coordinateSlabBox c r ρ) := hl'
    _ ≤ stdGaussian (Space (n+1)) (e ⁻¹' T) := measure_mono hs
    _ = stdGaussian (Space (n+1)) T := by
      rw [← Measure.map_apply e.continuous.measurable hT,stdGaussian_map]

end Falconer

end OAI
