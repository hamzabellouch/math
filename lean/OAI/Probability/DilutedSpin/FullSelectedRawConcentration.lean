import OAI.Probability.DilutedSpin.FullCountCorrection
import OAI.Probability.DilutedSpin.FullSelectedConcentration

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

noncomputable def fullSelectedRawScore
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) : ℝ :=
  packRoot (fun h k x n y => selectedScore T Q m (base h k x) (rootArray n y) sel fixed D E t u) z

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X] [MeasurableSpace Y] in
theorem fullSelectedRawScore_eq
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t : ℝ) (z : FullRootState Y X I M) (u : ℝ) :
    fullSelectedRawScore T Q m base sel fixed D E t z u =
    fullSelectedScore T Q m base sel fixed D E t z u-(4*u)*(z.2.2.1:ℝ) := by
  unfold fullSelectedRawScore fullSelectedScore packRoot
  ring

/-- The actual selected score, with the auxiliary convex correction removed. -/
theorem full_selected_root_concentration
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
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
    let G := fullSelectedRawScore T Q m base sel fixed D E t
    (∫ u in a..b, (∫ z, |G z u-∫ w, G w u ∂fullRootLaw ξ μ ν r s| ∂fullRootLaw ξ μ ν r s))/(b-a) ≤
      4*Real.sqrt (3*C^2*(r:ℝ)+4*(s:ℝ)+∑ j, (fieldBound j)^2/2)/ρ+12*ρ*(s:ℝ)/(b-a)+Real.sqrt s := by
  let G := fullSelectedScore T Q m base sel fixed D E t
  let P := fullRootLaw ξ μ ν r s
  have hI : Icc a b ⊆ Ioo (-(1:ℝ)/4) (1/4) := by
    intro u hu
    exact hJ ⟨by linarith [hu.1],by linarith [hu.2]⟩
  have hu (u : ℝ) (h : u ∈ Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI h).1],(hI h).2.le⟩
  have hbG (z : FullRootState Y X I M) (u : ℝ) (h : u ∈ Icc a b) :
      |G z u| ≤ 3*(z.2.2.1:ℝ) := by
    rw [show G z u = _ from fullSelectedScore_eq T Q m base sel fixed D E t z u]
    exact KernelTower.correctedPerturbScore_bound _ _ _ _ _
      (selectedCoefficient_bound _ sel D hD) (selectedCoefficient_bound _ sel E hE) ht (hu u h)
  have hcor := fullRoot_deviation_sub_count_integral ξ μ ν r s
    (measurable_fullSelectedScore T Q m base sel fixed D E t hbmeas)
    (((fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)).const_mul 3)
    hab.le hbG (show Measurable (fun u : ℝ => 4*u) from measurable_const.mul measurable_id)
    (fun u h => by rw [abs_mul]; norm_num; linarith [hu u h])
  have hmain := full_selected_corrected_concentration μ ν ξ r s T Q m hm base hbmeas
    sel fixed D E hC hb hf hD hE hrep hadd fieldBound hfield ht hab hρ hJ
  dsimp only at hmain ⊢
  change (∫ u in a..b, rootDeviation P (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u))/(b-a) ≤ _
  simp_rw [fullSelectedRawScore_eq]
  have hh := div_le_div_of_nonneg_right hcor (sub_pos.mpr hab).le
  rw [add_div,mul_div_cancel_left₀ _ (ne_of_gt (sub_pos.mpr hab))] at hh
  exact hh.trans (add_le_add hmain le_rfl)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
