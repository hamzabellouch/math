import OAI.Probability.DilutedSpin.CountedSteps

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem selectedFactor_log_bound (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t u : ℝ} (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) :
    |Real.log (selectedFactor sel fixed D E t u i x y)| ≤ 1 := by
  unfold selectedFactor
  split
  · have ht' := mul_le_mul_of_nonneg_left (hD i x y) (abs_nonneg t)
    have hu' := mul_le_mul_of_nonneg_left (hE i x y) (abs_nonneg u)
    rw [← abs_mul,mul_one] at ht' hu'
    have hlo : (1:ℝ)/2 ≤ 1+t*D i x y+u*E i x y := by
      linarith [(abs_le.mp (ht'.trans ht)).1,(abs_le.mp (hu'.trans hu)).1]
    have hhi : 1+t*D i x y+u*E i x y ≤ (3:ℝ)/2 := by
      linarith [(abs_le.mp (ht'.trans ht)).2,(abs_le.mp (hu'.trans hu)).2]
    have hpos : 0 < 1+t*D i x y+u*E i x y := by linarith
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hinv : (1+t*D i x y+u*E i x y)⁻¹ ≤ 2 := by
      apply (inv_le_iff_one_le_mul₀ hpos).mpr
      linarith
    have hlogInv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hlogInv
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · exact hf i x y

/-- Joint parameter regularity of the fully tilted selected score at fixed
labels. The countable random labels are reintroduced below. -/
theorem measurable_selected_correctedScore {X : Type} [MeasurableSpace X]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y)) (t : ℝ) :
    Measurable (fun z : X × ℝ => selectedScore T Q m (base z.1) roots sel fixed D E t z.2+4*n*z.2) := by
  have hh := KernelTower.measurable_correctedPerturbScore (tower roots L T Q) m
    (base := fun z : X × ℝ => otherLog (base z.1) roots sel fixed)
    (D := fun _ : X × ℝ => selectedCoefficient roots sel D)
    (E := fun _ : X × ℝ => selectedCoefficient roots sel E)
    (t := fun _ : X × ℝ => t) (u := fun z => z.2)
    (fun y => ((hb (physical roots L y)).comp measurable_fst).add measurable_const)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) measurable_const measurable_snd
  simpa only [corrected_score_eq] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
