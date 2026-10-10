import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderCompactCalculus
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderCutoffBounds
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ClassicalUniqueness

namespace OAI

/-! Differentiation of the actual localized difference energy. This uses
only classical regularity, before invoking the equations of motion. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector Set MeasureTheory
open scoped Topology

theorem cylinderWeight_compactSupport (n : ℕ) : HasCompactSupport (cylinderWeight n) := by
  have h := concentrationCutoff_compactSupport (by positivity : 0 < (n : ℝ) + 1)
    (0 : Plane)
  have hm : HasCompactSupport
      (concentrationCutoff ((n : ℝ) + 1) 0 * concentrationCutoff ((n : ℝ) + 1) 0) :=
    h.mul_right
  have he : cylinderWeight n =
      concentrationCutoff ((n : ℝ) + 1) 0 * concentrationCutoff ((n : ℝ) + 1) 0 := by
    funext x
    exact pow_two _
  rw [he]
  exact hm

theorem localizedDifferenceEnergy_hasDerivAt {ν : ℝ} {f u v : Velocity} {p q : Pressure}
    (hu : IsCylinderClassicalSolution ν f u p) (hv : IsCylinderClassicalSolution ν f v q)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (localizedDifferenceEnergy u v n)
      (2 * ∫ y, cylinderWeight n y.1 *
        dot (cylinderDifference u v t (atHeight y.1 y.2))
          (initialTimeDerivative u t (atHeight y.1 y.2) -
            initialTimeDerivative v t (atHeight y.1 y.2)) ∂cylinderMeasure) t := by
  let W : ℝ × (Plane × ℝ) → Space :=
    fun y => cylinderDifference u v y.1 (atHeight y.2.1 y.2.2)
  let G : ℝ × (Plane × ℝ) → Space := fun y =>
    initialTimeDerivative u y.1 (atHeight y.2.1 y.2.2) -
      initialTimeDerivative v y.1 (atHeight y.2.1 y.2.2)
  let φ : Plane → ℝ := cylinderWeight n
  have hmap : Continuous (fun y : ℝ × (Plane × ℝ) =>
      (y.1, atHeight y.2.1 y.2.2)) := by
    apply Continuous.prodMk continuous_fst
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [atHeight] <;> fun_prop
  have hW : ContinuousOn W (Icc 0 (t + 1) ×ˢ univ) := by
    apply ((hu.regularity.continuous_u (t + 1) (by linarith)).sub
      (hv.regularity.continuous_u (t + 1) (by linarith))).comp hmap.continuousOn
    intro y hy
    exact ⟨hy.1, mem_univ _⟩
  have hG : ContinuousOn G (Icc 0 (t + 1) ×ˢ univ) := by
    apply ((hu.regularity.continuous_ut (t + 1) (by linarith)).sub
      (hv.regularity.continuous_ut (t + 1) (by linarith))).comp hmap.continuousOn
    intro y hy
    exact ⟨hy.1, mem_univ _⟩
  have hφ : Continuous (fun y : ℝ × (Plane × ℝ) => φ y.2.1) :=
    (cylinderWeight_smooth n).continuous.comp (continuous_fst.comp continuous_snd)
  have hd (s : ℝ) (hs : s ∈ Ioo 0 (t + 1)) (y : Plane × ℝ) :
      HasDerivAt (fun r => φ y.1 * dot (W (r, y)) (W (r, y)))
        (φ y.1 * (2 * dot (W (s, y)) (G (s, y)))) s := by
    apply HasDerivAt.const_mul
    apply hasDerivAt_dot_self
    change HasDerivAt (fun r => u (r, atHeight y.1 y.2) - v (r, atHeight y.1 y.2))
      (initialTimeDerivative u s (atHeight y.1 y.2) -
        initialTimeDerivative v s (atHeight y.1 y.2)) s
    exact ((hu.regularity.temporal_u s hs.1.le (atHeight y.1 y.2)).hasDerivWithinAt.hasDerivAt
      (Ici_mem_nhds hs.1)).sub
      ((hv.regularity.temporal_u s hs.1.le (atHeight y.1 y.2)).hasDerivWithinAt.hasDerivAt
        (Ici_mem_nhds hs.1))
  have hzero (x : Plane) (hx : x ∉ tsupport φ) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  have h := CylinderLocalCalculus.supported_integral_hasDerivAt
    (g := fun y => φ y.2.1 * dot (W y) (W y))
    (d := fun y => φ y.2.1 * (2 * dot (W y) (G y)))
    (hφ.continuousOn.mul (dot_continuousOn hW hW))
    (hφ.continuousOn.mul (continuousOn_const.mul (dot_continuousOn hW hG))) hd
    (cylinderWeight_compactSupport n)
    (fun r y hy => by simp only [hzero y.1 hy, zero_mul])
    (fun y hy => by simp only [hzero y.1 hy, zero_mul])
    (show t ∈ Ioo 0 (t + 1) from ⟨ht, by linarith⟩)
  have he : (fun y : Plane × ℝ => φ y.1 * (2 * dot (W (t, y)) (G (t, y)))) =
      (fun y => 2 * (φ y.1 * dot (W (t, y)) (G (t, y)))) := by
    funext y
    ring
  change HasDerivAt (localizedDifferenceEnergy u v n)
    (∫ y, φ y.1 * (2 * dot (W (t, y)) (G (t, y))) ∂cylinderMeasure) t at h
  rw [he, integral_const_mul] at h
  exact h

end ForcedComputation.VelocityDetector

end

end OAI
