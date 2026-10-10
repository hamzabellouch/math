import OAI.Probability.BenjaminiSchramm.EntropyEvent
import OAI.Probability.UnimodularPercolation.Exploration.Marked

namespace OAI

namespace Percolation.BenjaminiSchramm

open CriticalPercolation.FiniteEntropy

namespace ProbeEntropy

open ProbeTree

theorem weight_pos (p h : ℝ) (hp : p ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1)
    (t : ProbeTree) (l : t.Leaf) : 0 < weight p h t l := by
  induction t with
  | done b => exact zero_lt_one
  | edge t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_pos (sub_pos.mpr hp.2) (ih₀ l)
    | inr l => exact mul_pos hp.1 (ih₁ l)
  | mark t₀ t₁ ih₀ ih₁ =>
    cases l with
    | inl l => exact mul_pos (sub_pos.mpr hh.2) (ih₀ l)
    | inr l => exact mul_pos hh.1 (ih₁ l)

noncomputable def totalQueries (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, weight p h t l * (queries t l : ℝ)

noncomputable def totalMarks (p h : ℝ) (t : ProbeTree) : ℝ :=
  ∑ l, weight p h t l * (marks t l : ℝ)

noncomputable def treeDivergence (p q h : ℝ) (t : ProbeTree) : ℝ :=
  divergence (weight p h t) (weight q h t)

@[simp] theorem totalQueries_done (p h : ℝ) (b : Bool) : totalQueries p h (.done b) = 0 := by
  simp [totalQueries,queries]

@[simp] theorem totalMarks_done (p h : ℝ) (b : Bool) : totalMarks p h (.done b) = 0 := by
  simp [totalMarks,marks]

theorem totalQueries_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalQueries p h (.edge t₀ t₁) =
      1 + (1-p) * totalQueries p h t₀ + p * totalQueries p h t₁ := by
  simp only [totalQueries,Fintype.sum_sum_type,weight,queries,Nat.cast_add,Nat.cast_one]
  simp_rw [mul_add,mul_one,mul_assoc]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,sum_weight,mul_one]
  ring

theorem totalQueries_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalQueries p h (.mark t₀ t₁) =
      (1-h) * totalQueries p h t₀ + h * totalQueries p h t₁ := by
  simp only [totalQueries,Fintype.sum_sum_type,weight,queries,mul_assoc,←Finset.mul_sum]

theorem totalMarks_edge (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalMarks p h (.edge t₀ t₁) =
      (1-p) * totalMarks p h t₀ + p * totalMarks p h t₁ := by
  simp only [totalMarks,Fintype.sum_sum_type,weight,marks,mul_assoc,←Finset.mul_sum]

theorem totalMarks_mark (p h : ℝ) (t₀ t₁ : ProbeTree) :
    totalMarks p h (.mark t₀ t₁) =
      1 + (1-h) * totalMarks p h t₀ + h * totalMarks p h t₁ := by
  simp only [totalMarks,Fintype.sum_sum_type,weight,marks,Nat.cast_add,Nat.cast_one]
  simp_rw [mul_add,mul_one,mul_assoc]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,sum_weight,mul_one]
  ring

theorem treeDivergence_edge (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t₀ t₁ : ProbeTree) :
    treeDivergence p q h (.edge t₀ t₁) = binaryDivergence p q +
      (1-p) * treeDivergence p q h t₀ + p * treeDivergence p q h t₁ := by
  have he : treeDivergence p q h (.edge t₀ t₁) =
      divergence (fun l => (1-p) * weight p h t₀ l) (fun l => (1-q) * weight q h t₀ l) +
      divergence (fun l => p * weight p h t₁ l) (fun l => q * weight q h t₁ l) := by
    simp only [treeDivergence,divergence,Fintype.sum_sum_type,weight]
  rw [he,divergence_mul _ _ (weight_pos p h hp hh t₀) (weight_pos q h hq hh t₀)
    (sum_weight p h t₀) _ _ (sub_pos.mpr hp.2) (sub_pos.mpr hq.2),
    divergence_mul _ _ (weight_pos p h hp hh t₁) (weight_pos q h hq hh t₁)
    (sum_weight p h t₁) _ _ hp.1 hq.1]
  dsimp [treeDivergence,binaryDivergence]
  ring

theorem treeDivergence_mark (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t₀ t₁ : ProbeTree) :
    treeDivergence p q h (.mark t₀ t₁) =
      (1-h) * treeDivergence p q h t₀ + h * treeDivergence p q h t₁ := by
  have he : treeDivergence p q h (.mark t₀ t₁) =
      divergence (fun l => (1-h) * weight p h t₀ l) (fun l => (1-h) * weight q h t₀ l) +
      divergence (fun l => h * weight p h t₁ l) (fun l => h * weight q h t₁ l) := by
    simp only [treeDivergence,divergence,Fintype.sum_sum_type,weight]
  rw [he,divergence_mul _ _ (weight_pos p h hp hh t₀) (weight_pos q h hq hh t₀)
    (sum_weight p h t₀) _ _ (sub_pos.mpr hh.2) (sub_pos.mpr hh.2),
    divergence_mul _ _ (weight_pos p h hp hh t₁) (weight_pos q h hq hh t₁)
    (sum_weight p h t₁) _ _ hh.1 hh.1]
  simp only [div_self (sub_pos.mpr hh.2).ne',div_self hh.1.ne',Real.log_one,mul_zero,add_zero,
    treeDivergence]

theorem treeDivergence_eq (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t : ProbeTree) :
    treeDivergence p q h t = binaryDivergence p q * totalQueries p h t := by
  induction t with
  | done b => simp [treeDivergence,divergence,weight]
  | edge t₀ t₁ ih₀ ih₁ =>
    rw [treeDivergence_edge p q h hp hq hh,totalQueries_edge,ih₀,ih₁]
    ring
  | mark t₀ t₁ ih₀ ih₁ =>
    rw [treeDivergence_mark p q h hp hq hh,totalQueries_mark,ih₀,ih₁]
    ring

theorem successMass_transfer (p q h : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (hq : q ∈ Set.Ioo 0 1) (hh : h ∈ Set.Ioo 0 1) (t : ProbeTree) :
    successMass q h t ≤ 2 * successMass p h t +
      2 * binaryDivergence p q * totalQueries p h t := by
  have hb := event_mass_le_two_add_divergence (weight p h t) (weight q h t)
    (outcome t) (fun l => (weight_pos p h hp hh t l).le)
    (fun l => (weight_pos q h hq hh t l).le) (sum_weight p h t) (sum_weight q h t)
    (fun l _ => weight_pos q h hq hh t l)
  change successMass q h t ≤ 2 * successMass p h t + 2 * treeDivergence p q h t at hb
  rw [treeDivergence_eq p q h hp hq hh] at hb
  simpa only [mul_assoc] using hb

theorem totalMarks_eq_successMass (p h : ℝ) {t : ProbeTree} (ht : IsMarkSearch t) :
    h * totalMarks p h t = successMass p h t := by
  induction ht with
  | fail => simp
  | @edge t₀ t₁ _ _ ih₀ ih₁ =>
    rw [totalMarks_edge,successMass_edge]
    rw [←ih₀,←ih₁]
    ring
  | @mark t₀ _ ih =>
    rw [totalMarks_mark,successMass_mark]
    simp only [totalMarks_done,successMass_done,ite_true,mul_zero,add_zero,mul_one]
    rw [←ih]
    ring

theorem totalQueries_le (p h : unitInterval) {t : ProbeTree} (ht : IsMarkSearch t)
    (d : ℕ) (hcost : ∀ l, queries t l ≤ d * marks t l) (hh : 0 < (h : ℝ)) :
    totalQueries p h t ≤ (d : ℝ) * successMass p h t / h := by
  apply (le_div_iff₀ hh).mpr
  have hb : totalQueries p h t ≤ (d : ℝ) * totalMarks p h t := by
    simp only [totalQueries,totalMarks,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have hh := mul_le_mul_of_nonneg_left
      (show (queries t l : ℝ) ≤ (d : ℝ) * marks t l by exact_mod_cast hcost l)
      (weight_nonneg p h t l)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hb hh.le
  rw [mul_assoc,mul_comm (totalMarks p h t) (h : ℝ),
    totalMarks_eq_successMass p h ht] at hm
  exact hm

end ProbeEntropy
end Percolation.BenjaminiSchramm

end OAI
