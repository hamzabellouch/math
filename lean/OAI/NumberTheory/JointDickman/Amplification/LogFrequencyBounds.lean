import OAI.NumberTheory.JointDickman.Probability.MajorArcHistogramBound

namespace OAI

/-! # Uniform frequency bounds for the logarithmic endpoint test -/

namespace JointDickman
open Finset MeasureTheory

theorem logOscillatoryTest_frequency_bounds {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {a b N M D : ℝ} (hb : 0 < b) (hN : 0 < N) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (w w' : ℝ → ℝ) (hw : ∀ t, HasDerivAt w (w' t) t)
    (hwb : ∀ t, |w t| ≤ M) (hw'b : ∀ t, |w' t| ≤ D) (β : ℝ) :
    let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
    let F := fun ξ => logOscillatoryTest w B N (β*ξ)
    let L := (D+2*Real.pi*|β| * M)*((B : ℝ)*(b*Real.exp 1))
    (∀ ξ, ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F ξ x‖ ≤ M) ∧
    (∀ ξ, ∀ i ∈ J, IntervalIntegrable (F ξ) volume
      (channelLower (channelFineCount m B) i) (channelUpper (channelFineCount m B) i)) ∧
    (∀ ξ, ∀ i ∈ J, ∀ u ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i),
      ∀ v ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F ξ u-F ξ v‖ ≤ (L*(1+|ξ|))*|u-v|) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro ξ i _ x _
    rw [logOscillatoryTest_norm]
    exact hwb _
  · intro ξ i _
    exact (logOscillatoryTest_continuous B N (β*ξ) hw).intervalIntegrable _ _
  · intro ξ i hi u hu v hv
    have hh := logOscillatoryTest_lipschitz (ω := β*ξ) (Nat.cast_nonneg B) hN hM hD hw
      (fun x hx => endpoint_histogram_window_scale hm hB hb hN hi hx) hwb hw'b hu hv
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    rw [abs_mul]
    have he : D+2*Real.pi*(|β| * |ξ|)*M ≤ (D+2*Real.pi*|β| * M)*(1+|ξ|) := by
      have hc : 0 ≤ 2*Real.pi*|β| * M := by positivity
      nlinarith [mul_nonneg hD (abs_nonneg ξ)]
    exact (mul_le_mul_of_nonneg_right he (by positivity)).trans_eq (by ring)

end JointDickman

end OAI
