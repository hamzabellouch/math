import OAI.Analysis.LipschitzHilbert.Geometry.RectangleLineCoordinates

namespace OAI

/-! A section-width estimate for projection onto a line. Applied to the
actual popularity sets in orthogonal rectangle coordinates. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem strip_projection_area (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (P : Set ℝ) (hP : MeasurableSet P) (a b c w : ℝ) (hb : b ≠ 0) (_hw : 0 ≤ w)
    (hproj : ∀ z ∈ E, z.1 ∈ P) (hstrip : ∀ z ∈ E, |a*z.1+b*z.2-c| ≤ w) :
    (volume.prod volume) E ≤ ENNReal.ofReal (2*w/|b|)*volume P := by
  have hsection (x : ℝ) : volume ((fun y => (x,y)) ⁻¹' E) ≤
      P.indicator (fun _ => ENNReal.ofReal (2*w/|b|)) x := by
    by_cases hx : x ∈ P
    · rw [indicator_of_mem hx]
      have hs : ((fun y => (x,y)) ⁻¹' E) ⊆
          (fun y : ℝ => b*y) ⁻¹' Icc (c-a*x-w) (c-a*x+w) := by
        intro y hy
        have h := abs_le.mp (hstrip (x,y) hy)
        constructor <;> dsimp at h ⊢ <;> linarith
      calc
        _ ≤ volume ((fun y : ℝ => b*y) ⁻¹' Icc (c-a*x-w) (c-a*x+w)) := measure_mono hs
        _ = ENNReal.ofReal |b⁻¹| * ENNReal.ofReal (2*w) := by
          rw [Real.volume_preimage_mul_left hb,Real.volume_Icc]
          congr 2
          ring
        _ = _ := by
          rw [←ENNReal.ofReal_mul (abs_nonneg _)]
          congr 1
          rw [abs_inv,div_eq_mul_inv]
          ring
    · rw [indicator_of_notMem hx]
      have hs : ((fun y => (x,y)) ⁻¹' E) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hx (hproj (x,y) hy)
      simp only [hs,measure_empty,le_refl]
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal (2*w/|b|)) x := lintegral_mono hsection
    _ = _ := by rw [lintegral_indicator hP,lintegral_const,Measure.restrict_apply_univ,mul_comm]

theorem strip_projection_area_half (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (P : Set ℝ) (hP : MeasurableSet P) (a b c w : ℝ) (hb : 1/2 ≤ |b|) (hw : 0 ≤ w)
    (hproj : ∀ z ∈ E, z.1 ∈ P) (hstrip : ∀ z ∈ E, |a*z.1+b*z.2-c| ≤ w) :
    (volume.prod volume) E ≤ ENNReal.ofReal (4*w)*volume P := by
  have hb0 : 0 < |b| := by linarith
  have hbne : b ≠ 0 := by intro he; norm_num [he] at hb
  refine (strip_projection_area E hE P hP a b c w hbne hw hproj hstrip).trans ?_
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hb0).mpr
  nlinarith

end LipschitzHilbert

end

end OAI
