import OAI.NumberTheory.Catalan.Analysis.ManuscriptNormLogVGroup056
import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneBracketHeight

namespace OAI

section

noncomputable section
namespace InternalCatalan

def manuscriptXLogFieldInterval (c v : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ) : ℚ × ℚ :=
  manuscriptIntervalAdd
    (manuscriptIntervalAdd
      (manuscriptIntervalAdd
        (manuscriptIntervalScale (19 / 48) (manuscriptScaledLogInterval m0 y0))
        (manuscriptIntervalScale (1 / 12) (manuscriptScaledLogInterval m1 y1)))
      (manuscriptIntervalScale (-c) (manuscriptScaledLogInterval m2 y2))) (v, v)

def manuscriptYLogFieldInterval (v : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ) : ℚ × ℚ :=
  manuscriptIntervalAdd
    (manuscriptIntervalAdd
      (manuscriptIntervalScale (7 / 48) (manuscriptScaledLogInterval m0 y0))
      (manuscriptIntervalScale (1 / 12) (manuscriptScaledLogInterval m1 y1))) (v, v)

theorem manuscript_x_log_field_interval (c v : ℚ) (s0 s1 s2 : ℝ)
    (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization s0 m0 y0)
    (h1 : Case1PointData.FixedLogNormalization s1 m1 y1)
    (h2 : Case1PointData.FixedLogNormalization s2 m2 y2) :
    (19 / 48 : ℝ) * Real.log s0 + (1 / 12 : ℝ) * Real.log s1 -
      (c : ℝ) * Real.log s2 + (v : ℝ) ∈
        Set.Icc ((manuscriptXLogFieldInterval c v m0 m1 m2 y0 y1 y2).1 : ℝ)
          ((manuscriptXLogFieldInterval c v m0 m1 m2 y0 y1 y2).2 : ℝ) := by
  have h := manuscript_interval_add
    (manuscript_interval_add
      (manuscript_interval_add
        (manuscript_interval_scale (19 / 48)
          (manuscript_fixed_log_interval m0 y0 h0.1 h0.2.1))
        (manuscript_interval_scale (1 / 12)
          (manuscript_fixed_log_interval m1 y1 h1.1 h1.2.1)))
      (manuscript_interval_scale (-c)
        (manuscript_fixed_log_interval m2 y2 h2.1 h2.2.1)))
    (show (v : ℝ) ∈ Set.Icc (((v, v) : ℚ × ℚ).1 : ℝ) (((v, v) : ℚ × ℚ).2 : ℝ)
      from ⟨le_rfl, le_rfl⟩)
  convert h using 1 <;> first | rfl | (push_cast; ring)

theorem manuscript_y_log_field_interval (v : ℚ) (s0 s1 : ℝ)
    (m0 m1 : ℤ) (y0 y1 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization s0 m0 y0)
    (h1 : Case1PointData.FixedLogNormalization s1 m1 y1) :
    (7 / 48 : ℝ) * Real.log s0 + (1 / 12 : ℝ) * Real.log s1 + (v : ℝ) ∈
      Set.Icc ((manuscriptYLogFieldInterval v m0 m1 y0 y1).1 : ℝ)
        ((manuscriptYLogFieldInterval v m0 m1 y0 y1).2 : ℝ) := by
  have h := manuscript_interval_add
    (manuscript_interval_add
      (manuscript_interval_scale (7 / 48)
        (manuscript_fixed_log_interval m0 y0 h0.1 h0.2.1))
      (manuscript_interval_scale (1 / 12)
        (manuscript_fixed_log_interval m1 y1 h1.1 h1.2.1)))
    (show (v : ℝ) ∈ Set.Icc (((v, v) : ℚ × ℚ).1 : ℝ) (((v, v) : ℚ × ℚ).2 : ℝ)
      from ⟨le_rfl, le_rfl⟩)
  convert h using 1 <;> first | rfl | (push_cast; ring)

theorem manuscript_case1X_interval (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization |(x : ℝ)| m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1)
    (h2 : Case1PointData.FixedLogNormalization (1 + (x : ℝ) ^ 2) m2 y2) :
    barrierCase1X (x : ℝ) ∈
      Set.Icc ((manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat x)
        m0 m1 m2 y0 y1 y2).1 : ℝ)
        ((manuscriptXLogFieldInterval (41 / 48) (barrierCase1XRat x)
          m0 m1 m2 y0 y1 y2).2 : ℝ) := by
  rw [barrierCase1X_eval_rat]
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    manuscript_x_log_field_interval (41 / 48) (barrierCase1XRat x)
      |(x : ℝ)| (1 - (x : ℝ)) (1 + (x : ℝ) ^ 2)
      m0 m1 m2 y0 y1 y2 h0 h1 h2

theorem manuscript_case1Y_interval (x : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization (x : ℝ) m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1) :
    barrierCase1Y (x : ℝ) ∈
      Set.Icc ((manuscriptYLogFieldInterval (barrierCase1YRat x) m0 m1 y0 y1).1 : ℝ)
        ((manuscriptYLogFieldInterval (barrierCase1YRat x) m0 m1 y0 y1).2 : ℝ) := by
  rw [barrierCase1Y_eval_rat]
  exact manuscript_y_log_field_interval (barrierCase1YRat x) (x : ℝ) (1 - (x : ℝ))
    m0 m1 y0 y1 h0 h1

end InternalCatalan

end

end

end OAI
