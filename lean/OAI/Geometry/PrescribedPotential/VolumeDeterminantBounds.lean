import Mathlib
import OAI.Geometry.PrescribedPotential.VolumeNormalization

namespace OAI

/-! Volume Determinant Bounds. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ComplexOrder Classical ContDiff
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma volumePath_logRatio_bound [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (ht : t ∈ Icc 0 1)
    (hp : g.PositivePotential φ)
    (he : ∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g h).value x+b)
    (x : X) : |(g.logRatio (g.deform φ hp)).value x| ≤
      2*‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖ := by
  let F : C(X,ℝ) := ⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩
  have hb := volumePath_scalar_bound g h ht ⟨hp,he⟩
  have hf : |t*(prescribedForcing g h).value x| ≤ ‖F‖ := by
    rw [abs_mul, abs_of_nonneg ht.1]
    apply (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)).trans
    simpa [F, Real.norm_eq_abs] using F.norm_coe_le_norm x
  rw [he x]
  exact (abs_add_le _ _).trans (by change _ ≤ 2*‖F‖; linarith)

 

theorem volumePath_det_ratio_bounds [CompactSpace X] [Nonempty X]
    (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {t b : ℝ} {φ : SmoothRealFunction A} (ht : t ∈ Icc 0 1)
    (hp : g.PositivePotential φ)
    (he : ∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g h).value x+b)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    let M := ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖;
    Real.exp (-2*M) ≤ (g.matrix i z + φ.hessian i z).det.re / (g.matrix i z).det.re ∧
    (g.matrix i z + φ.hessian i z).det.re / (g.matrix i z).det.re ≤ Real.exp (2*M) := by
  let M := ‖(⟨(prescribedForcing g h).value, (prescribedForcing g h).continuous⟩ : C(X,ℝ))‖
  let x := (A.chart i).symm z
  have hi : x ∈ (A.chart i).source := (A.chart i).mapsTo_symm hz
  have hl := volumePath_logRatio_bound g h ht hp he x
  change |g.logRatioValue (g.deform φ hp) x| ≤ 2*M at hl
  rw [g.logRatioValue_local _ i hi, (A.chart i).right_inv hz] at hl
  have heq : (g.matrix i z + φ.hessian i z).det.re / (g.matrix i z).det.re =
      Real.exp (Real.log ((g.deform φ hp).volumeCoefficient i z) - Real.log (g.volumeCoefficient i z)) := by
    rw [Real.exp_sub, Real.exp_log ((g.deform φ hp).volumeCoefficient_pos i hz),
      Real.exp_log (g.volumeCoefficient_pos i hz)]
    rfl
  rw [heq]
  obtain ⟨hlo,hup⟩ := abs_le.mp hl
  exact ⟨Real.exp_le_exp.mpr (by simpa only [neg_mul] using hlo), Real.exp_le_exp.mpr hup⟩
end Anticanonical.SourceSmooth

end
end

end OAI
