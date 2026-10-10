import OAI.MeasureTheory.Falconer.Estimates.RegularizationProperties
import OAI.MeasureTheory.Falconer.Recursion.ProfileContactStability

namespace OAI

/-! # Fixed contact intervals for actual regularized source-class profiles -/

namespace Falconer.Regularization
open Set MeasureTheory Filter
open scoped Topology NNReal
variable {d : ℕ}

theorem actual_profile_sequence_contact (Q : ℕ → DyadicCube d)
    (μ : ℕ → Measure (Space d)) (N B : ℕ → ℕ) (p : ℕ → CellPath d)
    (hN : ∀ i, 0 < N i) (hB : ∀ i, 0 < B i)
    {s q t : ℝ} (hs : 0 ≤ s) (hqt : q < t) (hts : t < s)
    (e : ℕ → ℝ) (he : Tendsto (fun i => e i+s/(N i:ℝ)) atTop (𝓝 0))
    (hgrid : ∀ i j, j ≤ N i → s*(j:ℝ)/(N i:ℝ)-e i ≤
      sourceProfile (Q i) (μ i) (N i) (B i) (p i) j) :
    ∃ A B' : ℝ, ∃ φ : ℕ → ℕ,
      0 < A ∧ A < B' ∧ B' < 1 ∧ B' < 2*A ∧ StrictMono φ ∧
      ∀ η > 0, ∃ I₀ : ℕ, ∀ i ≥ I₀,
        (∀ w ∈ Icc 0 A, q*w-η ≤ sourceUnitProfile (Q (φ i)) (μ (φ i))
          (N (φ i)) (B (φ i)) (p (φ i)) w) ∧
        (∀ w ∈ Icc A B', t*(w-A)-η ≤ sourceUnitProfile (Q (φ i)) (μ (φ i))
          (N (φ i)) (B (φ i)) (p (φ i)) w-
            sourceUnitProfile (Q (φ i)) (μ (φ i)) (N (φ i)) (B (φ i)) (p (φ i)) A) ∧
        (∀ w ∈ Icc B' 1, q*(w-B')-η ≤ sourceUnitProfile (Q (φ i)) (μ (φ i))
          (N (φ i)) (B (φ i)) (p (φ i)) w-
            sourceUnitProfile (Q (φ i)) (μ (φ i)) (N (φ i)) (B (φ i)) (p (φ i)) B') := by
  apply profile_sequence_contact (fun i => sourceUnitProfile (Q i) (μ i) (N i) (B i) (p i))
    (fun i => (sourceUnitProfile_properties (Q i) (μ i) (hN i) (hB i) (p i)).2.2.2.1)
    (fun i => (sourceUnitProfile_properties (Q i) (μ i) (hN i) (hB i) (p i)).2.1) he
    (fun i u hu => ?_) hqt hts
  have hh := sourceUnitProfile_lower_from_grid (Q i) (μ i) (hN i) (hB i) (p i) hs
    (hgrid i) hu
  linarith

end Falconer.Regularization

end OAI
