import Mathlib
import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Recursion.ClassConditional

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open PlanarFalconer
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

theorem projection_shifted_band_boundND (μ : Measure V) [IsFiniteMeasure μ]
    (e : V) {w : ℝ} (hw : 0 < w) (C s : ℝ) :
    (μ.prod μ) {z : V × V | |inner ℝ (z.1-z.2) e-s| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : V × V | |inner ℝ (z.1-z.2) e| ≤ w} := by
  let f : V → ℝ := fun y => inner ℝ y e
  have hf : Measurable f := by dsimp [f]; fun_prop
  let ν := Measure.map f μ
  have he (v s : ℝ) :
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2-s| ≤ v} =
      (μ.prod μ) {z : V × V | |inner ℝ (z.1-z.2) e-s| ≤ v} := by
    rw [show ν.prod ν = Measure.map (Prod.map f f) (μ.prod μ) from
      Measure.map_prod_map μ μ hf hf,Measure.map_apply (hf.prodMap hf) (by measurability)]
    congr 1
    ext z
    have hdot : f z.1-f z.2 = inner ℝ (z.1-z.2) e := by simp only [f,inner_sub_left]
    change |f z.1-f z.2-s| ≤ v ↔ _
    rw [hdot]
    rfl
  have h := real_bin_shifted_self_band_bound ν hw C s
  rw [he] at h
  have hz := he w 0
  simp only [sub_zero] at hz
  rwa [hz] at h

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem affine_distance_collisionND {x x' y y' e : V} {w : ℝ}
    (hx : |dist x y-inner ℝ (x-y) e| ≤ w)
    (hx' : |dist x' y'-inner ℝ (x'-y') e| ≤ w)
    (hc : |dist x y-dist x' y'| ≤ w) :
    |inner ℝ (y-y') e-inner ℝ (x-x') e| ≤ 3*w := by
  have he : inner ℝ (y-y') e-inner ℝ (x-x') e =
      -(inner ℝ (x-y) e-inner ℝ (x'-y') e) := by simp only [inner_sub_left]; ring
  rw [he,abs_neg]
  obtain ⟨h₁,h₂⟩ := abs_le.mp hx
  obtain ⟨h₃,h₄⟩ := abs_le.mp hx'
  obtain ⟨h₅,h₆⟩ := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
