import OAI.Analysis.PlanarEndpoint.Information.FiniteTables
import OAI.Analysis.PlanarEndpoint.Information.Logarithms
import OAI.Analysis.PlanarEndpoint.Information.TailBounds

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace PlanarEndpoint.TransverseInformation

variable {S V Y : Type*} [Fintype S] [Fintype V] [Fintype Y]

open scoped Classical in
def sampledTable (w : S → ℝ) (v : S → V) (y : S → Y) (b : V) (a : Y) : ℝ :=
  ∑ s, if v s = b ∧ y s = a then w s else 0

omit [Fintype V] [Fintype Y] in
lemma sampledTable_nonneg (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (v : S → V) (y : S → Y) (b : V) (a : Y) : 0 ≤ sampledTable w v y b a := by
  classical
  unfold sampledTable
  exact Finset.sum_nonneg (fun s _ => by split_ifs; exact hw s; exact le_rfl)

lemma sampledTable_sum (w : S → ℝ) (v : S → V) (y : S → Y) (f : V → Y → ℝ) :
    (∑ b, ∑ a, sampledTable w v y b a * f b a) = ∑ s, w s * f (v s) (y s) := by
  classical
  unfold sampledTable
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ b, ∑ s, ∑ a, (if v s = b ∧ y s = a then w s else 0) * f b a := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ s, ∑ b, ∑ a, (if v s = b ∧ y s = a then w s else 0) * f b a := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp [ite_and, ite_mul, eq_comm]

lemma sampledTable_total (w : S → ℝ) (v : S → V) (y : S → Y) :
    (∑ b, ∑ a, sampledTable w v y b a) = ∑ s, w s := by
  simpa only [mul_one] using sampledTable_sum w v y (fun _ _ => 1)

def sampledInformation (L : ℝ) (w : S → ℝ) (v : S → V) (y : S → Y) (s : S) : ℝ :=
  information L (conditionalMass (sampledTable w v y) (v s) (y s))

lemma sampledInformation_nonneg (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (v : S → V) (y : S → Y) {L : ℝ} (hL : 1 < L) (s : S) :
    0 ≤ sampledInformation L w v y s :=
  conditional_information_nonneg _ (sampledTable_nonneg w hw v y) hL _ _

lemma sampledInformation_mass_tail_le (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (v : S → V) (y : S → Y) {L A : ℝ} (hL : 1 < L) :
    (∑ s, if A < sampledInformation L w v y s then w s else 0) ≤
      (Fintype.card Y : ℝ) * L ^ (-A) := by
  classical
  unfold sampledInformation
  calc
    _ = ∑ s, w s * (if A < information L
        (conditionalMass (sampledTable w v y) (v s) (y s)) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    _ = ∑ b, ∑ a, sampledTable w v y b a * (if A < information L
        (conditionalMass (sampledTable w v y) b a) then 1 else 0) :=
      (sampledTable_sum w v y (fun b a => if A < information L
        (conditionalMass (sampledTable w v y) b a) then (1 : ℝ) else 0)).symm
    _ = ∑ b, ∑ a, if A < information L (conditionalMass (sampledTable w v y) b a)
        then sampledTable w v y b a else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ ≤ _ := conditional_information_mass_tail_le _ (sampledTable_nonneg w hw v y)
      (by rw [sampledTable_total, hw1]) hL

lemma sampledInformation_expected_tail_le (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hw1 : ∑ s, w s = 1) (v : S → V) (y : S → Y) {L A : ℝ} (hL : 1 < L) :
    (∑ s, if A < sampledInformation L w v y s then
      w s * sampledInformation L w v y s else 0) ≤
      (Fintype.card Y : ℝ) * (2 / Real.log L) * Real.sqrt (L ^ (-A)) := by
  classical
  unfold sampledInformation
  calc
    _ = ∑ s, w s * (if A < information L
        (conditionalMass (sampledTable w v y) (v s) (y s)) then
        information L (conditionalMass (sampledTable w v y) (v s) (y s)) else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      split_ifs <;> simp
    _ = ∑ b, ∑ a, sampledTable w v y b a * (if A < information L
        (conditionalMass (sampledTable w v y) b a) then
        information L (conditionalMass (sampledTable w v y) b a) else 0) :=
      (sampledTable_sum w v y (fun b a => if A < information L
        (conditionalMass (sampledTable w v y) b a) then
        information L (conditionalMass (sampledTable w v y) b a) else 0)).symm
    _ = ∑ b, ∑ a, if A < information L (conditionalMass (sampledTable w v y) b a)
        then sampledTable w v y b a * information L (conditionalMass (sampledTable w v y) b a)
        else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ ≤ _ := conditional_information_expected_tail_le _ (sampledTable_nonneg w hw v y)
      (by rw [sampledTable_total, hw1]) hL

end PlanarEndpoint.TransverseInformation
end

end OAI
