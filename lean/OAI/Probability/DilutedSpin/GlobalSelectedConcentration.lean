import OAI.Probability.DilutedSpin.GlobalSelectedAverage

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- An unconditional quantitative bound for the global-centered selected score
on the actual two-Poisson-plus-field law. Selection changes no prior and does
not discard any of the other perturbations. -/
theorem full_selected_error_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) {c : ℝ} (hc : 0 < c) (hm : ∀ j, c ≤ m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (fixed i x y)| ≤ 1)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (fieldBound : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ fieldBound j)
    {t a b ρ : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hρ : 0 < ρ)
    (hJ : Icc (a-ρ) (b+ρ) ⊆ Ioo (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u)/(b-a) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))/(b-a)+
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+
      12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  have hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4) := by
    intro u hu
    have hh := hJ (show u ∈ Icc (a-ρ) (b+ρ) from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
    exact ⟨hh.1.le,hh.2.le⟩
  have h1 := full_selected_error_split_average ξ μ ν r s T Q m base hbmeas sel fixed D E
    hD hE ht hab hc hm hI
  have h2 := full_selected_root_concentration μ ν ξ r s T Q m (fun j => hc.trans_le (hm j))
    base hbmeas sel fixed D E hC hb hf hD hE hrep hadd fieldBound hfield ht hab hρ hJ
  have hh := div_le_div_of_nonneg_right h1 (sub_pos.mpr hab).le
  rw [add_div] at hh
  exact hh.trans (by dsimp only [rootDeviation]; dsimp only at h2; linarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
