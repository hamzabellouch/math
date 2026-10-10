import OAI.Analysis.LipschitzHilbert.Estimates.HilbertVariation

namespace OAI

/-! Realification preserves the cubic variation and the terminal L² norm
of the complex Hilbert-valued packet sums. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

def complexRealify {κ : Type*} [Fintype κ] (v : EuclideanSpace ℂ κ) :
    EuclideanSpace ℝ (κ × Fin 2) :=
  WithLp.toLp 2 (fun i => if i.2 = 0 then (v i.1).re else (v i.1).im)

theorem complexRealify_sub {κ : Type*} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    complexRealify (v - w) = complexRealify v - complexRealify w := by
  ext ⟨k,j⟩
  fin_cases j <;> simp [complexRealify]

theorem norm_complexRealify {κ : Type*} [Fintype κ] (v : EuclideanSpace ℂ κ) :
    ‖complexRealify v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simpa [complexRealify, Fin.sum_univ_two, Complex.normSq_apply, pow_two] using
    Complex.normSq_eq_norm_sq (v k)

theorem finiteCubicVariation_complexRealify {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    finiteCubicVariation (fun n => complexRealify (F n)) N = finiteCubicVariation F N := by
  have hnorm (i j : ℕ) : ‖complexRealify (F i) - complexRealify (F j)‖ = ‖F i - F j‖ := by
    rw [← complexRealify_sub, norm_complexRealify]
  unfold finiteCubicVariation
  simp_rw [hnorm]

/-- Apply the scalar published input to real and imaginary coordinates.
Realification preserves both norms exactly, so there is no dimension loss. -/
theorem lepingle_complex_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ k, Martingale (fun n x => (F n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (F n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (F n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (F n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_euclidean_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ F hFre hFim hF2re hF2im N
  let H := fun n x => complexRealify (F n x)
  have hH (i : κ × Fin 2) : Martingale (fun n x => H n x i) ℱ μ := by
    rcases i with ⟨k,j⟩
    fin_cases j
    · simpa [H, complexRealify] using hFre k
    · simpa [H, complexRealify] using hFim k
  have hH2 (i : κ × Fin 2) (n : ℕ) : MemLp (fun x => H n x i) 2 μ := by
    rcases i with ⟨k,j⟩
    fin_cases j
    · simpa [H, complexRealify] using hF2re k n
    · simpa [H, complexRealify] using hF2im k n
  have h := hbound Ω m μ hμ (κ × Fin 2) ℱ H hH hH2 N
  simpa only [H, finiteCubicVariation_complexRealify, ← ofReal_norm, norm_complexRealify] using h

end LipschitzHilbert

end

end OAI
