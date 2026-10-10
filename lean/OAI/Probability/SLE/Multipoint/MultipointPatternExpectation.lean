import OAI.Probability.SLE.Multipoint.MultipointStoppedProduct
import OAI.Probability.SLE.Multipoint.MultipointSwitchPatterns

namespace OAI

/-! Summing the conditional product estimate over the actual finite
switch partition, then telescoping the downward product jumps. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem switchPattern_integral_le
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (P : Measure Ω)
    (s : Finset ι) (ρ : ι → Ω → ℝ≥0) (τ : Ω → ℝ≥0)
    (hA : ∀ A ∈ s.powerset, MeasurableSet (switchPatternEvent s ρ τ A))
    (F G : Finset ι → Ω → ℝ) (X Y : Ω → ℝ)
    (hF : ∀ A ∈ s.powerset, IntegrableOn (F A) (switchPatternEvent s ρ τ A) P)
    (hG : ∀ A ∈ s.powerset, IntegrableOn (G A) (switchPatternEvent s ρ τ A) P)
    (hFX : ∀ A ∈ s.powerset, ∀ ω ∈ switchPatternEvent s ρ τ A, F A ω = X ω)
    (hGY : ∀ A ∈ s.powerset, ∀ ω ∈ switchPatternEvent s ρ τ A, G A ω = Y ω)
    (hle : ∀ A ∈ s.powerset,
      (∫ ω in switchPatternEvent s ρ τ A, F A ω ∂P) ≤
        ∫ ω in switchPatternEvent s ρ τ A, G A ω ∂P) :
    Integrable X P ∧ Integrable Y P ∧ (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  have heX := sum_switchPattern_fields s ρ τ F X hFX
  have heY := sum_switchPattern_fields s ρ τ G Y hGY
  have hFi (A : Finset ι) (hAs : A ∈ s.powerset) :
      Integrable ((switchPatternEvent s ρ τ A).indicator (F A)) P :=
    (integrable_indicator_iff (hA A hAs)).mpr (hF A hAs)
  have hGi (A : Finset ι) (hAs : A ∈ s.powerset) :
      Integrable ((switchPatternEvent s ρ τ A).indicator (G A)) P :=
    (integrable_indicator_iff (hA A hAs)).mpr (hG A hAs)
  have hXi : Integrable X P := by
    rw [← heX]
    exact integrable_finsetSum _ hFi
  have hYi : Integrable Y P := by
    rw [← heY]
    exact integrable_finsetSum _ hGi
  refine ⟨hXi,hYi,?_⟩
  rw [← heX, ← heY, integral_finsetSum _ hFi, integral_finsetSum _ hGi]
  apply Finset.sum_le_sum
  intro A hAs
  rw [integral_indicator (hA A hAs), integral_indicator (hA A hAs)]
  exact hle A hAs

theorem finite_switched_product_expectation_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : ℕ)
    (X Y : ℕ → Ω → ℝ)
    (hX : ∀ n, n ≤ N → Integrable (X n) P)
    (hY : ∀ n, n < N → Integrable (Y n) P)
    (hflow : ∀ n, n < N → (∫ ω, Y n ω ∂P) ≤ ∫ ω, X n ω ∂P)
    (hjump : ∀ n, n < N → ∀ ω, X (n+1) ω ≤ Y n ω) :
    (∫ ω, X N ω ∂P) ≤ ∫ ω, X 0 ω ∂P := by
  have hind : ∀ n, n ≤ N → (∫ ω, X n ω ∂P) ≤ ∫ ω, X 0 ω ∂P := by
    intro n
    induction n with
    | zero => exact fun _ => le_rfl
    | succ n ih =>
      intro hn
      have hnN : n < N := Nat.lt_of_succ_le hn
      have hle : (∫ ω, X (n+1) ω ∂P) ≤ ∫ ω, Y n ω ∂P :=
        integral_mono_ae (hX (n+1) hn) (hY n hnN) (ae_of_all _ (hjump n hnN))
      exact hle.trans ((hflow n hnN).trans (ih (Nat.le_trans (Nat.le_succ n) hn)))
  exact hind N le_rfl

end SLEExactGauge.Multipoint

end

end OAI
