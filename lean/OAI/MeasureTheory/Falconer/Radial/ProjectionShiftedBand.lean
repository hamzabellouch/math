import OAI.MeasureTheory.Falconer.Angular.ActualAngularTests
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem projection_shifted_band_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    (e : Plane) {w : ℝ} (hw : 0 < w) (C s : ℝ) :
    (μ.prod μ) {z : Plane × Plane | |planeDot (z.1-z.2) e-s| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : Plane × Plane | |planeDot (z.1-z.2) e| ≤ w} := by
  let f : Plane → ℝ := fun y => planeDot y e
  have hf : Measurable f := by dsimp [f,planeDot]; fun_prop
  let ν := Measure.map f μ
  have he (v s : ℝ) :
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2-s| ≤ v} =
      (μ.prod μ) {z : Plane × Plane | |planeDot (z.1-z.2) e-s| ≤ v} := by
    rw [show ν.prod ν = Measure.map (Prod.map f f) (μ.prod μ) from
      Measure.map_prod_map μ μ hf hf,Measure.map_apply (hf.prodMap hf) (by measurability)]
    congr 1
    ext z
    have hdot : f z.1-f z.2 = planeDot (z.1-z.2) e := by simp [f,planeDot]; ring
    change |f z.1-f z.2-s| ≤ v ↔ _
    rw [hdot]
    rfl
  have h := real_bin_shifted_self_band_bound ν hw C s
  rw [he] at h
  have hz := he w 0
  simp only [sub_zero] at hz
  rwa [hz] at h

theorem affine_distance_collision {x x' y y' e : Plane} {w : ℝ}
    (hx : |dist x y-planeDot (x-y) e| ≤ w)
    (hx' : |dist x' y'-planeDot (x'-y') e| ≤ w)
    (hc : |dist x y-dist x' y'| ≤ w) :
    |planeDot (y-y') e-planeDot (x-x') e| ≤ 3*w := by
  have he : planeDot (y-y') e-planeDot (x-x') e =
      -(planeDot (x-y) e-planeDot (x'-y') e) := by simp [planeDot]; ring
  rw [he,abs_neg]
  obtain ⟨h₁,h₂⟩ := abs_le.mp hx
  obtain ⟨h₃,h₄⟩ := abs_le.mp hx'
  obtain ⟨h₅,h₆⟩ := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end PlanarFalconer

end OAI
