import OAI.Analysis.LipschitzHilbert.Trees.LineGridMartingale
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteMeasureLepingle
import OAI.Analysis.LipschitzHilbert.Estimates.PerturbedLepingle

namespace OAI

/-! Complex Hilbert-valued averages on the actual finite line grid. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem lintegral_square_condExp_le {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (m' : MeasurableSpace Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ‖μ[f | m'] x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := ENNReal.rpow_le_rpow
    (eLpNorm_condExp_le_eLpNorm (m := m') (m0 := m) (μ := μ) f
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 2)
  have hleft := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (hf.condExp (m := m') (by norm_num)).aestronglyMeasurable
  have hright := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    hf.aestronglyMeasurable
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h hleft hright
  rwa [hleft, hright] at h

theorem enorm_complex_sq (z : ℂ) : ‖z‖ₑ ^ 2 = ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2 := by
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  have h : ‖z‖ * ‖z‖ = z.re * z.re + z.im * z.im := by
    simpa only [pow_two, Complex.normSq_apply] using (Complex.normSq_eq_norm_sq z).symm
  simp only [Real.norm_eq_abs, pow_two]
  nlinarith only [h, sq_abs z.re, sq_abs z.im]

theorem lintegral_complex_euclidean_sq {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (F : Ω → EuclideanSpace ℂ κ) (hF : Measurable F) :
    (∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ) = ∑ k,
      ((∫⁻ x, ‖(F x k).re‖ₑ ^ 2 ∂μ) + (∫⁻ x, ‖(F x k).im‖ₑ ^ 2 ∂μ)) := by
  have hpoint (x : Ω) : ‖F x‖ₑ ^ 2 = ∑ k, (‖(F x k).re‖ₑ ^ 2 + ‖(F x k).im‖ₑ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_complex_sq]
  simp_rw [hpoint]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_add_left]
    exact ((Complex.continuous_re.comp ((PiLp.continuous_apply 2 _ k))).measurable.comp hF).enorm.pow_const _
  · intro k _
    exact (((Complex.continuous_re.comp (PiLp.continuous_apply 2 _ k)).measurable.comp hF).enorm.pow_const _).add
      (((Complex.continuous_im.comp (PiLp.continuous_apply 2 _ k)).measurable.comp hF).enorm.pow_const _)

namespace FiniteLineGrid

def complexAverage {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => (g.average μ (fun y => (F y k).re) n x : ℂ) +
    g.average μ (fun y => (F y k).im) n x * Complex.I)

theorem complexAverage_re {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) (k : κ) :
    (g.complexAverage μ F n x k).re = g.average μ (fun y => (F y k).re) n x := by
  simp [complexAverage]

theorem complexAverage_im {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) (k : κ) :
    (g.complexAverage μ F n x k).im = g.average μ (fun y => (F y k).im) n x := by
  simp [complexAverage]

theorem complexAverage_measurable {κ : Type*} [Fintype κ] (g : FiniteLineGrid)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) :
    Measurable (g.complexAverage μ F n) := by
  apply measurable_complex_martingale
  · intro k
    simpa only [complexAverage_re] using g.average_martingale μ (fun y => (F y k).re)
  · intro k
    simpa only [complexAverage_im] using g.average_martingale μ (fun y => (F y k).im)

theorem complexAverage_energy {κ : Type*} [Fintype κ] (g : FiniteLineGrid)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → EuclideanSpace ℂ κ) (hF : Measurable F)
    (hRe : ∀ k, MemLp (fun y => (F y k).re) 2 μ)
    (hIm : ∀ k, MemLp (fun y => (F y k).im) 2 μ) (n : ℕ) :
    (∫⁻ x, ‖g.complexAverage μ F n x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
  rw [lintegral_complex_euclidean_sq μ _ (g.complexAverage_measurable μ F n),
    lintegral_complex_euclidean_sq μ F hF]
  apply Finset.sum_le_sum
  intro k _
  simp only [complexAverage_re, complexAverage_im, average]
  exact add_le_add (lintegral_square_condExp_le μ _ _ (hRe k))
    (lintegral_square_condExp_le μ _ _ (hIm k))

end FiniteLineGrid

/-- The actual line-cell averages satisfy the published variation bound,
with the norm of the original function on the right. -/
theorem lineGrid_lepingle (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (κ : Type) [Fintype κ]
      (F : ℝ → EuclideanSpace ℂ κ), Measurable F →
      (∀ k, MemLp (fun x => (F x k).re) 2 g.lineMeasure) →
      (∀ k, MemLp (fun x => (F x k).im) 2 g.lineMeasure) → ∀ N : ℕ,
        (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
          (fun n => g.complexAverage g.lineMeasure F n x) N) ^ (2 / 3 : ℝ) ∂g.lineMeasure) ≤
          (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_finite_measure hL
  refine ⟨C,hC,?_⟩
  intro g κ inst F hF hRe hIm N
  have h := hbound ℝ inferInstance g.lineMeasure inferInstance κ g.filtration
    (g.complexAverage g.lineMeasure F)
    (fun k => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.average_martingale g.lineMeasure (fun x => (F x k).re))
    (fun k => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.average_martingale g.lineMeasure (fun x => (F x k).im))
    (fun k n => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.average_memLp g.lineMeasure _ (hRe k) n)
    (fun k n => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.average_memLp g.lineMeasure _ (hIm k) n) N
  exact h.trans (mul_le_mul_right (g.complexAverage_energy g.lineMeasure F hF hRe hIm N) _)

/-- The comparison term is the sum of squared differences
between smooth partial sums and cell means. -/
theorem lineGrid_variation_comparison (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (κ : Type) [Fintype κ]
      (F : ℝ → EuclideanSpace ℂ κ) (P : ℕ → ℝ → EuclideanSpace ℂ κ),
      Measurable F → (∀ n, Measurable (P n)) →
      (∀ k, MemLp (fun x => (F x k).re) 2 g.lineMeasure) →
      (∀ k, MemLp (fun x => (F x k).im) 2 g.lineMeasure) → ∀ N : ℕ,
        (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ)
          ∂g.lineMeasure) ≤
          2 * (C : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖F x‖ₑ ^ 2 ∂g.lineMeasure) +
            8 * ∑ k : Fin (N + 1), ∫⁻ x,
              ‖P k x - g.complexAverage g.lineMeasure F k x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lineGrid_lepingle hL
  refine ⟨C,hC,?_⟩
  intro g κ inst F P hF hP hRe hIm N
  have h := lintegral_finiteCubicVariation_comparison g.lineMeasure P
    (g.complexAverage g.lineMeasure F) hP (g.complexAverage_measurable g.lineMeasure F) N
  exact h.trans (add_le_add (by
    simpa only [mul_assoc] using mul_le_mul_right (hbound g κ F hF hRe hIm N) 2) le_rfl)

end LipschitzHilbert

end

end OAI
