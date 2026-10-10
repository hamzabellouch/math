import OAI.Analysis.LipschitzHilbert.Fourier.ScalarLineVariation

namespace OAI

/-! Start the actual mesh martingale at a prescribed finer level. This
allows the surrounding finite root interval to grow without changing
the packet scales used in the comparison. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert
namespace FiniteLineGrid

def shiftedFiltration (g : FiniteLineGrid) (offset : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq i := g.filtration (offset + i)
  mono' := fun _ _ h => g.filtration.mono (Nat.add_le_add_left h offset)
  le' i := g.filtration.le (offset + i)

theorem shifted_average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (offset : ℕ) :
    Martingale (fun i => g.average μ f (offset + i)) (g.shiftedFiltration offset) μ :=
  martingale_condExp f (g.shiftedFiltration offset) μ

end FiniteLineGrid

theorem lineGrid_shifted_lepingle (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (offset : ℕ) (κ : Type) [Fintype κ]
      (F : ℝ → EuclideanSpace ℂ κ), Measurable F →
      (∀ k, MemLp (fun x => (F x k).re) 2 g.lineMeasure) →
      (∀ k, MemLp (fun x => (F x k).im) 2 g.lineMeasure) → ∀ N : ℕ,
        (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
          (fun i => g.complexAverage g.lineMeasure F (offset + i) x) N) ^ (2 / 3 : ℝ) ∂g.lineMeasure) ≤
          (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_finite_measure hL
  refine ⟨C,hC,?_⟩
  intro g offset κ inst F hF hRe hIm N
  have h := hbound ℝ inferInstance g.lineMeasure inferInstance κ (g.shiftedFiltration offset)
    (fun i => g.complexAverage g.lineMeasure F (offset + i))
    (fun k => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.shifted_average_martingale g.lineMeasure (fun x => (F x k).re) offset)
    (fun k => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.shifted_average_martingale g.lineMeasure (fun x => (F x k).im) offset)
    (fun k i => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.average_memLp g.lineMeasure _ (hRe k) (offset + i))
    (fun k i => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.average_memLp g.lineMeasure _ (hIm k) (offset + i)) N
  exact h.trans (mul_le_mul_right (g.complexAverage_energy g.lineMeasure F hF hRe hIm (offset + N)) _)

theorem scalar_shifted_line_comparison (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (offset : ℕ)
      (f : ℝ → ℂ) (P : ℕ → ℝ → ℂ), Measurable f →
      (∀ i, Measurable (P i)) → MemLp f 2 g.lineMeasure → ∀ N : ℕ,
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => P i x) N) ^ (2 / 3 : ℝ)
        ∂g.lineMeasure) ≤
      2 * (C : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂g.lineMeasure) +
        8 * ∑ i : Fin (N + 1), ∫⁻ x,
          ‖P i.val x - g.scalarAverage g.lineMeasure f (offset + i.val) x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lineGrid_shifted_lepingle hL
  refine ⟨C,hC,?_⟩
  intro g offset f P hf hP hf2 N
  let F := fun x => scalarVector (f x)
  let Q := fun i x => scalarVector (P i x)
  let M := fun i => g.complexAverage g.lineMeasure F (offset + i)
  have h := lintegral_finiteCubicVariation_comparison g.lineMeasure Q M
    (fun i => scalarVector_measurable.comp (hP i))
    (fun i => g.complexAverage_measurable g.lineMeasure F (offset + i)) N
  have hm := hbound g offset Unit F (scalarVector_measurable.comp hf)
    (fun _ => hf2.re) (fun _ => hf2.im) N
  have ht := h.trans (add_le_add (by
    simpa only [mul_assoc] using mul_le_mul_right hm 2) le_rfl)
  simpa only [Q, M, F, finiteCubicVariation_scalarVector, scalarVector_average,
    ← scalarVector_sub, ← ofReal_norm, norm_scalarVector, mul_assoc] using ht

end LipschitzHilbert

end

end OAI
