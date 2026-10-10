import OAI.Analysis.PlanarEndpoint.Information.FiniteLaws
import OAI.Analysis.PlanarEndpoint.Information.Sampling

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal Classical
namespace PlanarEndpoint.TransverseInformation

variable {S : Type} [Fintype S] {V Y : ℕ → Type}
  [∀ i, Fintype (V i)] [∀ i, Fintype (Y i)]

def informationVector (L : ℝ) (w : S → ℝ)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) (s : S) : ℕ → ℝ :=
  fun i => sampledInformation L w (v i) (y i) s

def sampledJointLaw (L : ℝ) (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) :
    ProbabilityMeasure (ℕ → ℝ) :=
  finiteInformationLaw w hw hw1 (informationVector L w v y)

lemma sampledJointLaw_nonneg (L : ℝ) (hL : 1 < L) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) (i : ℕ) :
    ∀ᵐ x ∂(sampledJointLaw L w hw hw1 v y : Measure (ℕ → ℝ)), 0 ≤ x i := by
  apply finiteInformationLaw_ae w hw hw1 (informationVector L w v y) (fun x => 0 ≤ x i)
  · exact measurableSet_le measurable_const (measurable_pi_apply i)
  · intro s _
    exact sampledInformation_nonneg w hw (v i) (y i) hL s

omit [∀ index, Fintype (V index)] in
lemma sampledJointLaw_integrable (L : ℝ) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) (i : ℕ) :
    Integrable (fun x => x i) (sampledJointLaw L w hw hw1 v y : Measure (ℕ → ℝ)) :=
  finiteInformationLaw_integrable w hw hw1 _ _ (measurable_pi_apply i)

omit [∀ index, Fintype (V index)] in
lemma sampledJointLaw_integral (L : ℝ) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) (i : ℕ) :
    (∫ x, x i ∂(sampledJointLaw L w hw hw1 v y : Measure (ℕ → ℝ))) =
      ∑ s, w s * sampledInformation L w (v i) (y i) s :=
  finiteInformationLaw_integral w hw hw1 _ _ (measurable_pi_apply i)

lemma sampledJointLaw_mass_tail_le (L : ℝ) (hL : 1 < L) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) (i : ℕ) (A : ℝ) :
    (sampledJointLaw L w hw hw1 v y : Measure (ℕ → ℝ)) {x | A < |x i|} ≤
      ENNReal.ofReal ((Fintype.card (Y i) : ℝ) * L ^ (-A)) := by
  change (finiteInformationLaw w hw hw1 (informationVector L w v y) : Measure (ℕ → ℝ)) _ ≤ _
  rw [finiteInformationLaw_apply _ _ _ _ _
    (isOpen_lt continuous_const (continuous_apply i).abs).measurableSet]
  apply ENNReal.ofReal_le_ofReal
  have heq : (∑ s, if |informationVector L w v y s i| > A then w s else 0) =
      ∑ s, if A < sampledInformation L w (v i) (y i) s then w s else 0 := by
    apply Finset.sum_congr rfl
    intro s _
    rw [informationVector, abs_of_nonneg (sampledInformation_nonneg w hw (v i) (y i) hL s)]
  change (∑ s, if A < |informationVector L w v y s i| then w s else 0) ≤ _
  rw [heq]
  exact sampledInformation_mass_tail_le w hw hw1 (v i) (y i) hL

lemma sampledJointLaw_expected_tail_le (L : ℝ) (hL : 1 < L) (w : S → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1)
    (v : (i : ℕ) → S → V i) (y : (i : ℕ) → S → Y i) (i : ℕ) (A : ℝ) :
    (∫ x, if A < x i then x i else 0
      ∂(sampledJointLaw L w hw hw1 v y : Measure (ℕ → ℝ))) ≤
      (Fintype.card (Y i) : ℝ) * (2 / Real.log L) * Real.sqrt (L ^ (-A)) := by
  have hm : Measurable (fun x : ℕ → ℝ => if A < x i then x i else 0) :=
    (measurable_pi_apply i).piecewise
      (isOpen_lt continuous_const (continuous_apply i)).measurableSet measurable_const
  change (∫ x, _ ∂(finiteInformationLaw w hw hw1 (informationVector L w v y) : Measure (ℕ → ℝ))) ≤ _
  rw [finiteInformationLaw_integral w hw hw1 _ _ hm]
  calc
    _ = ∑ s, if A < sampledInformation L w (v i) (y i) s then
        w s * sampledInformation L w (v i) (y i) s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      unfold informationVector
      split_ifs <;> simp
    _ ≤ _ := sampledInformation_expected_tail_le w hw hw1 (v i) (y i) hL

end PlanarEndpoint.TransverseInformation
end

end OAI
