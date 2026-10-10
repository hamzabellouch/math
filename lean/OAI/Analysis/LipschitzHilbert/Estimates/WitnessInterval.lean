import OAI.Analysis.LipschitzHilbert.Fourier.WitnessLineAverage

namespace OAI

/-! A concrete interval carries each transferred compact witness. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.SlopeBox

def witnessInterval (T : SlopeBox) (P : ℝ) : Set ℝ :=
  Icc (T.x - P * T.length) (T.x + P * T.length)

theorem horizontal_distance_le_radius (T : SlopeBox) (z : ℝ × ℝ) :
    |z.1 - T.x| ≤ T.radius z * T.length := by
  have hh : |T.horizontal z| ≤ T.radius z := by
    unfold radius
    exact le_add_of_nonneg_right (abs_nonneg _)
  unfold horizontal at hh
  rw [abs_div, abs_of_pos T.length_pos] at hh
  exact (div_le_iff₀ T.length_pos).mp hh

theorem mem_witnessInterval (T : SlopeBox) {P : ℝ} {z : ℝ × ℝ}
    (hz : T.radius z ≤ P) : z.1 ∈ T.witnessInterval P := by
  have h := (T.horizontal_distance_le_radius z).trans
    (mul_le_mul_of_nonneg_right hz T.length_pos.le)
  have ha := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

theorem witnessInterval_length (T : SlopeBox) {P : ℝ} (hP : 0 ≤ P) :
    volume.real (T.witnessInterval P) = 2 * P * T.length := by
  rw [witnessInterval, Real.volume_real_Icc_of_le (by nlinarith [T.length_pos])]
  ring

/-- The witness produces the required average on a concrete interval that
also contains the evaluation point, with no further interval selection. -/
theorem witness_centered_line_average (T : SlopeBox) (E : Set (ℝ × ℝ)) (hE : IsCompact E)
    {A q P : ℝ} (hA : 0 < A) (hq : 0 ≤ q) (hP : 0 < P) (hAP : A ≤ P)
    (hbox : ∀ w ∈ E, T.radius w ≤ A)
    (harea : q * T.length * T.width ≤ (volume.prod volume).real E)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (s : ℝ) (z : ℝ × ℝ)
    (hz : T.radius z ≤ P) (bin : Set ℝ) (hbin : MeasurableSet bin)
    (htransfer : ∀ w ∈ E, u (referencePoint s z w) ∈ bin) :
    z.1 ∈ T.witnessInterval P ∧
      q / (4 * A * P) ≤
        (∫ x in T.witnessInterval P, (LipschitzHilbert.lineBinSet u s z bin).indicator
          (fun _ => (1 : ℝ)) x) / volume.real (T.witnessInterval P) := by
  refine ⟨T.mem_witnessInterval hz, ?_⟩
  have hl := T.length_pos
  have hlen := T.witnessInterval_length hP.le
  have havg := T.witness_line_average E hE hA hq (mul_pos (by norm_num : (0 : ℝ) < 2) hP)
    hbox harea u hu s z bin (T.witnessInterval P) hbin measure_Icc_lt_top.ne
    (by rw [hlen]; positivity) (by rw [hlen])
    (fun w hw => T.mem_witnessInterval ((hbox w hw).trans hAP)) htransfer
  convert havg using 1
  ring

end LipschitzHilbert.SlopeBox

end

end OAI
