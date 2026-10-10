import OAI.Analysis.PlanarEndpoint.Information.DeterminationLimits
import OAI.Analysis.PlanarEndpoint.Information.MixedLaws
import OAI.Analysis.PlanarEndpoint.Information.MixedLimits
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S : ℕ → Type} [∀ n, Fintype (S n)]
  {V Y : ℕ → ℕ → Type} [∀ n i, Fintype (V n i)] [∀ n i, Fintype (Y n i)]
  (L : ℕ → ℝ) (w : (n : ℕ) → S n → ℝ)
  (hw : ∀ n s, 0 ≤ w n s) (hw1 : ∀ n, ∑ s, w n s = 1)
  (v : (n i : ℕ) → S n → V n i) (y : (n i : ℕ) → S n → Y n i)
  (P : (n : ℕ) → ℕ → S n → Prop)

def originalEventObservables (n i : ℕ) (s : S n) : ℝ := if P n i s then 1 else 0

omit [∀ index, Fintype (S index)] in
lemma originalEventObservables_bound (n i : ℕ) (s : S n) :
    |originalEventObservables P n i s| ≤ 1 := by
  unfold originalEventObservables
  split_ifs <;> norm_num

theorem exists_original_information_event_limit (hL : ∀ n, 2 ≤ L n)
    (hLlim : Tendsto L atTop atTop) (c : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (C i)))
    (hcard : ∀ n i, (Fintype.card (Y n i) : ℝ) ≤ (L n) ^ (c n i)) :
    ∃ μ : ProbabilityMeasure ((ℕ ⊕ ℕ) → ℝ), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto
        ((mixedInformationLaws L w hw hw1 v y (originalEventObservables P)) ∘ φ)
        atTop (𝓝 μ) ∧
      (∀ᵐ x ∂(μ : Measure ((ℕ ⊕ ℕ) → ℝ)),
        (∀ i, 0 ≤ x (.inl i) ∧ x (.inl i) ≤ C i) ∧
        (∀ i, x (.inr i) = 0 ∨ x (.inr i) = 1)) ∧
      ∀ i, Integrable (fun x => x (.inl i)) (μ : Measure ((ℕ ⊕ ℕ) → ℝ)) ∧
        Tendsto (fun n => ∑ s, w (φ n) s *
          sampledInformation (L (φ n)) (w (φ n)) (v (φ n) i) (y (φ n) i) s)
          atTop (𝓝 (∫ x, x (.inl i) ∂(μ : Measure ((ℕ ⊕ ℕ) → ℝ)))) := by
  obtain ⟨μ, φ, hφ, hμ, hsupp, hmeans⟩ :=
    exists_mixed_information_sharp_limit L w hw hw1 v y (originalEventObservables P)
      hL hLlim c C hc hcard (fun _ => 1) (originalEventObservables_bound P)
  have hbool : ∀ i, ∀ᵐ x ∂(μ : Measure ((ℕ ⊕ ℕ) → ℝ)),
      x (.inr i) = 0 ∨ x (.inr i) = 1 := by
    intro i
    apply ae_indicator_in_limit (fun n => w (φ n)) (fun n => hw (φ n))
      (fun n => hw1 (φ n))
      (fun n => mixedInformationVector (L (φ n)) (w (φ n))
        (v (φ n)) (y (φ n)) (originalEventObservables P (φ n)))
      hμ (continuous_apply (Sum.inr i : ℕ ⊕ ℕ))
    intro n s _
    change (if P (φ n) i s then (1 : ℝ) else 0) = 0 ∨
      (if P (φ n) i s then (1 : ℝ) else 0) = 1
    split_ifs <;> simp
  exact ⟨μ, φ, hφ, hμ, hsupp.and (ae_all_iff.mpr hbool), hmeans⟩

end PlanarEndpoint.TransverseInformation
end

end OAI
