import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings

namespace OAI

/-!
Pairings with finite step functions reduce to sums of cell integrals and cell means.
Convergence of cell masses and means therefore gives convergence of these pairings.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

theorem integral_mul_finiteStep (μ : Measure X)
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (w : X → ℝ) (hw : Integrable w μ) (c : ι → ℝ) :
    (∫ x, w x * finiteStep s c x ∂μ) = ∑ i, (∫ x in s i, w x ∂μ) * c i := by
  classical
  have heq : (fun x => w x * finiteStep s c x) =
      (fun x => ∑ i, (s i).indicator (fun y => w y * c i) x) := by
    funext x
    simp only [finiteStep, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ s i <;> simp [hx]
  rw [heq, integral_finsetSum _ (fun i _ => (hw.mul_const (c i)).indicator (hs i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hs i), integral_mul_const]

theorem integral_mul_finiteStep_cellMeans (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (w : X → ℝ) (hw : MemLp w 2 μ) (c : ι → ℝ)
    (hm : ∀ i, μ.real (s i) ≠ 0) :
    (∫ x, w x * finiteStep s c x ∂μ) =
      ∑ i, μ.real (s i) * (cellMean (μ.restrict (s i)) w * c i) := by
  rw [integral_mul_finiteStep μ s hs w (hw.integrable (by norm_num)) c]
  apply Finset.sum_congr rfl
  intro i _
  have hmass : (μ.restrict (s i)).real univ ≠ 0 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using! hm i
  have heq := cellMean_mul_mass (μ.restrict (s i)) w hmass
  simp only [Measure.real, Measure.restrict_apply_univ] at heq
  change (∫ x in s i, w x ∂μ) * c i = _
  rw [← heq]
  simp only [Measure.real]
  ring

theorem cellMean_step_pairing_tendsto (μ : ℕ → Measure X) (ν : Measure X)
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (w : ℕ → X → ℝ)
    (hw : ∀ j, MemLp (w j) 2 (μ j)) (b c : ι → ℝ)
    (hb : ∀ i, Tendsto (fun j => cellMean ((μ j).restrict (s i)) (w j)) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (ν.real (s i))))
    (hpos : ∀ᶠ j in atTop, ∀ i, (μ j).real (s i) ≠ 0) :
    Tendsto (fun j => ∫ x, w j x * finiteStep s c x ∂μ j) atTop
      (𝓝 (∫ x, finiteStep s b x * finiteStep s c x ∂ν)) := by
  have hprod : (fun x => finiteStep s b x * finiteStep s c x) =
      finiteStep s (fun i => b i * c i) := by
    classical
    funext x
    by_cases hx : ∃ i, x ∈ s i
    · obtain ⟨i, hi⟩ := hx
      rw [finiteStep_eq_cell s b hd i x hi, finiteStep_eq_cell s c hd i x hi,
        finiteStep_eq_cell s _ hd i x hi]
    · have hn : ∀ i, x ∉ s i := fun i hi => hx ⟨i, hi⟩
      simp [finiteStep, hn]
  rw [hprod, integral_finiteStep ν s hs]
  have heq : (fun j => ∫ x, w j x * finiteStep s c x ∂μ j) =ᶠ[atTop]
      (fun j => ∑ i, (μ j).real (s i) * (cellMean ((μ j).restrict (s i)) (w j) * c i)) := by
    filter_upwards [hpos] with j hj
    exact integral_mul_finiteStep_cellMeans (μ j) s hs (w j) (hw j) c hj
  apply (tendsto_congr' heq).mpr
  exact tendsto_finsetSum _ fun i _ => (hm i).mul ((hb i).mul_const (c i))

end

end RieszRectifiability

end OAI
