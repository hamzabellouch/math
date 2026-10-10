import OAI.InformationTheory.QuantumCircuit.CommonAxes
import OAI.InformationTheory.QuantumCircuit.ProductState

namespace OAI

/-! Distribution of excitation patterns in a product basis. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

def outcomeMass {N : ℕ} (M : Count N) (ψ : State N) (F : Finset (Fin N)) : ℝ :=
  ‖act (M.pattern F) ψ‖^2

def meanCount {N : ℕ} (M : Count N) (ψ : State N) : ℝ :=
  ∑ F ∈ M.support.powerset, (F.card : ℝ) * outcomeMass M ψ F

lemma outcomeMass_nonneg {N : ℕ} (M : Count N) (ψ : State N) (F : Finset (Fin N)) :
    0 ≤ outcomeMass M ψ F := sq_nonneg _

lemma outcomeMass_total (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (M : Count N) (ψ : State N) :
    ∑ F ∈ M.support.powerset, outcomeMass M ψ F = ‖ψ‖^2 := by
  symm
  have h := hspec.pythagoras M.support.powerset M.pattern ψ
    (fun F _ => M.pattern_projection F) (fun F hF G hG hFG => by
      rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG),
        ite_eq_right hFG])
  simpa only [M.sum_pattern, act_one, outcomeMass] using h

lemma outcomeMass_high (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (M : Count N) (ψ : State N) (r : ℝ) :
    ∑ F ∈ M.support.powerset.filter (fun F => r ≤ (F.card : ℝ)), outcomeMass M ψ F =
      ‖act (M.high r) ψ‖^2 := by
  symm
  rw [M.high_eq_sum_filter]
  exact hspec.pythagoras _ M.pattern ψ (fun F _ => M.pattern_projection F)
    (fun F hF G hG hFG => by
      rw [M.pattern_mul (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1), ite_eq_right hFG])

lemma meanCount_le_cut (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (M : Count N) (ψ : State N) {r : ℝ} (hr : 0 ≤ r) :
    meanCount M ψ ≤ r * ‖ψ‖^2 + N * ‖act (M.high r) ψ‖^2 := by
  rw [← outcomeMass_total hspec M ψ, ← outcomeMass_high hspec M ψ,
    Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro F hF
  have hfN : (F.card : ℝ) ≤ N := by
    exact_mod_cast (show F.card ≤ N by simpa using
      (Finset.card_le_card (Finset.mem_powerset.mp hF)).trans (Finset.card_le_univ _))
  have hm := outcomeMass_nonneg M ψ F
  by_cases hf : r ≤ (F.card : ℝ)
  · simp only [hf, ite_true]
    nlinarith [mul_le_mul_of_nonneg_right hfN hm]
  · simp only [hf, ite_false, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right (not_le.mp hf).le hm

lemma Count.Subcount.pattern_eq {N : ℕ} {A M : Count N}
    (h : A.Subcount M) (F : Finset (Fin N)) :
    A.pattern F = (M.restrict A.support).pattern F := by
  classical
  unfold Count.pattern Count.restrict
  congr 1
  funext i
  by_cases hi : i ∈ A.support
  · simp [hi, h.1 hi, h.2 i hi]
  · simp [hi]

lemma meanCount_subcount (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (A M : Count N) (h : A.Subcount M) (ψ : State N) :
    meanCount A ψ = ∑ F ∈ M.support.powerset,
      ((F ∩ A.support).card : ℝ) * outcomeMass M ψ F := by
  have hh := hspec.restriction_moment M A.support ψ
  have hs : (M.restrict A.support).support = A.support := Finset.inter_eq_right.mpr h.1
  rw [hs] at hh
  simpa only [meanCount, outcomeMass, h.pattern_eq] using hh

lemma meanCount_join (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (A B : Count N) (h : Disjoint A.support B.support) (ψ : State N) :
    meanCount (A.join B) ψ = meanCount A ψ + meanCount B ψ := by
  classical
  rw [meanCount_subcount hspec A (A.join B) (Count.subcount_join_left A B),
    meanCount_subcount hspec B (A.join B) (Count.subcount_join_right A B h),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  have hdis : Disjoint (F ∩ A.support) (F ∩ B.support) :=
    h.mono Finset.inter_subset_right Finset.inter_subset_right
  have hu : F ∩ A.support ∪ F ∩ B.support = F := by
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left]
    exact Finset.mem_powerset.mp hF
  have hc := Finset.card_union_of_disjoint hdis
  rw [hu] at hc
  change (F.card : ℝ) * outcomeMass (A.join B) ψ F = _
  rw [hc]
  push_cast
  ring

lemma meanCount_joint (hspec : PublishedProductSpectralResolution)
    {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) (ψ : State N) :
    meanCount (jointTest l) ψ = (l.map (fun A => meanCount A ψ)).sum := by
  induction l with
  | nil => simp [jointTest, meanCount, Count.empty, outcomeMass]
  | cons A l ih =>
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hl
    rw [jointTest, meanCount_join hspec A _ (jointTest_disjoint A l ha), ih hl]
    rfl

end QAC

end

end OAI
