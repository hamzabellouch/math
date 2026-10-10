import OAI.Analysis.FiniteFactor.CrossedProduct.AngleLaw
import OAI.Analysis.FiniteFactor.CrossedProduct.StageCoupling

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Fractional-part threshold in the small phase range, with both signs. -/
theorem phase_threshold_of_abs {a t : ℝ} (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hlo : a ≤ |t|) (hhi : |t| ≤ 1/2) :
    1 - Int.fract t ∈ Set.Icc a (1-a) := by
  have ht0 : |t| ≠ 0 := ne_of_gt (ha.trans_le hlo)
  have hf : Int.fract |t| = |t| := Int.fract_eq_self.mpr ⟨abs_nonneg _, by linarith⟩
  rcases le_total 0 t with hp | hn
  · rw [abs_of_nonneg hp] at hf hlo hhi
    rw [hf]
    constructor <;> linarith
  · have he : t = -|t| := by rw [abs_of_nonpos hn]; ring
    rw [he, Int.fract_neg (by rw [hf]; exact ht0), hf]
    constructor <;> linarith

/-- Phase bounds for every stage and realization.
There is no eventual-stage or probabilistic assumption. -/
theorem SourceAngles.first_phase {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (s : ℕ) (k : ℤ)
    (hlo : (sourceStageState s).G * (sourceStageState s).K ≤ |(k : ℝ)|)
    (hhi : |(k : ℝ)| ≤ ((sourceBlockSize s : ℝ) * (sourceStageState s).K)/4)
    (i : Fin (sourceBlockSize s)) :
    1 - Int.fract ((k : ℝ)*θ ⟨s,i⟩) ∈
      Set.Icc ((sourceStageState s).G/(sourceBlockSize s : ℝ))
        (1-(sourceStageState s).G/(sourceBlockSize s : ℝ)) := by
  have hm := sourceBlockSize_pos s
  have hK := sourceCutoff_pos s
  have hG : 0 < (sourceStageState s).G := lt_of_lt_of_le zero_lt_one (sourceStageState s).G_ge
  have ha4 : (sourceStageState s).G / (sourceBlockSize s : ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ hm).mpr
    have hh := (sourceStage s).m_ge_G
    change 4*(sourceStageState s).G ≤ (sourceBlockSize s : ℝ) at hh
    linarith
  apply phase_threshold_of_abs (div_pos hG hm) ha4
  · rw [abs_mul, abs_of_nonneg (hθ.nonneg ⟨s,i⟩)]
    calc
      (sourceStageState s).G / (sourceBlockSize s : ℝ) =
          ((sourceStageState s).G*(sourceStageState s).K) *
            (1/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) := by field_simp
      _ ≤ |(k : ℝ)| *θ ⟨s,i⟩ :=
        mul_le_mul hlo (hθ ⟨s,i⟩).1 (by positivity) (abs_nonneg _)
  · rw [abs_mul, abs_of_nonneg (hθ.nonneg ⟨s,i⟩)]
    calc
      |(k : ℝ)| *θ ⟨s,i⟩ ≤
          (((sourceBlockSize s : ℝ)*(sourceStageState s).K)/4) *
            (2/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) :=
        mul_le_mul hhi (hθ ⟨s,i⟩).2 (hθ.nonneg _) (by positivity)
      _ = 1/2 := by field_simp; norm_num

end
end FiniteFactor

end OAI
