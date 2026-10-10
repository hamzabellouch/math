import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.MixedLaws
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S : Type} [Fintype S] {V Y : ℕ → Type}
  [∀ i, Fintype (V i)] [∀ i, Fintype (Y i)]

lemma mixedInformationLaw_nonneg (L : ℝ) (hL : 1 < L) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (i : ℕ) :
    ∀ᵐ x ∂(mixedInformationLaw L w hw hw1 v y z : Measure ((ℕ ⊕ ℕ) → ℝ)),
      0 ≤ x (.inl i) := by
  apply finiteInformationLaw_ae w hw hw1 (mixedInformationVector L w v y z)
    (fun x => 0 ≤ x (.inl i))
  · exact measurableSet_le measurable_const (measurable_pi_apply _)
  · intro s _
    exact sampledInformation_nonneg w hw (v i) (y i) hL s

omit [∀ index, Fintype (V index)] in
lemma mixedInformationLaw_integrable (L : ℝ) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (i : ℕ) :
    Integrable (fun x => x (.inl i))
      (mixedInformationLaw L w hw hw1 v y z : Measure ((ℕ ⊕ ℕ) → ℝ)) :=
  finiteInformationLaw_integrable w hw hw1 _ _ (measurable_pi_apply _)

omit [∀ index, Fintype (V index)] in
lemma mixedInformationLaw_integral (L : ℝ) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (i : ℕ) :
    (∫ x, x (.inl i)
      ∂(mixedInformationLaw L w hw hw1 v y z : Measure ((ℕ ⊕ ℕ) → ℝ))) =
      ∑ s, w s * sampledInformation L w (v i) (y i) s :=
  finiteInformationLaw_integral w hw hw1 _ _ (measurable_pi_apply _)

lemma mixedInformationLaw_expected_tail_le (L : ℝ) (hL : 1 < L) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i)
    (z : ℕ → S → ℝ) (i : ℕ) (A : ℝ) :
    (∫ x, if A < x (.inl i) then x (.inl i) else 0
      ∂(mixedInformationLaw L w hw hw1 v y z : Measure ((ℕ ⊕ ℕ) → ℝ))) ≤
      (Fintype.card (Y i) : ℝ) * (2 / Real.log L) * Real.sqrt (L ^ (-A)) := by
  have hm : Measurable (fun x : (ℕ ⊕ ℕ) → ℝ =>
      if A < x (.inl i) then x (.inl i) else 0) :=
    (measurable_pi_apply (Sum.inl i : ℕ ⊕ ℕ)).piecewise
      (isOpen_lt continuous_const (continuous_apply (Sum.inl i : ℕ ⊕ ℕ))).measurableSet
      measurable_const
  change (∫ x, _ ∂(finiteInformationLaw w hw hw1
    (mixedInformationVector L w v y z) : Measure ((ℕ ⊕ ℕ) → ℝ))) ≤ _
  rw [finiteInformationLaw_integral w hw hw1 _ _ hm]
  calc
    _ = ∑ s, if A < sampledInformation L w (v i) (y i) s then
        w s * sampledInformation L w (v i) (y i) s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      change w s * (if A < sampledInformation L w (v i) (y i) s then
        sampledInformation L w (v i) (y i) s else 0) = _
      by_cases h : A < sampledInformation L w (v i) (y i) s <;> simp [h]
    _ ≤ _ := sampledInformation_expected_tail_le w hw hw1 (v i) (y i) hL

end PlanarEndpoint.TransverseInformation
end

end OAI
