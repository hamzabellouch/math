import OAI.Analysis.TriangularHilbert.SortedWindows

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def maskedArray (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ) (s : ℝ) : Three → Matrix ι ι ℂ :=
  replaceZero A (fun i j => windowMask (a i j) (b i j) s (A 0 i j))

def maskedCost (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (h : ℝ) (u : ι → ℝ) (r : Three) (s : ℝ) : ℝ :=
  ∑ v, planeIntegral (fun p => heatCost (maskedArray A a b s) h u p (fun z => strictRate r z*s) v v) 0

omit [Fintype ι] [DecidableEq ι] in
lemma maskedArray_const (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    (k : ℕ) {s : ℝ} (hs : s ∈ Set.Ico (sortedTimes S hS k) (sortedTimes S hS (k+1))) :
    maskedArray A a b s = maskedArray A a b (sortedTimes S hS k) := by
  unfold maskedArray
  congr 1
  funext i j
  exact sortedTimes_mask_const S hS k (ha i j) (hb i j) hs _

lemma planeSumCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (r : Three) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => ∑ v, planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b := by
  have hi : IntervalIntegrable (∑ v : Three, fun s => planeIntegral (fun p => heatCost A h u p (fun z => strictRate r z*s) v v) d) volume a b :=
    IntervalIntegrable.sum Finset.univ (fun v _ => (planeTime_intervalIntegrable A hh u d (strictRate r) (strictRate_pos r) ha hab).2 v v)
  convert hi using 1
  ext s
  simp

lemma maskedCost_interval_piece (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (ht0 : 0 < sortedTimes S hS 0) (r : Three) (k : ℕ) :
    IntervalIntegrable (maskedCost A a b h u r) volume (sortedTimes S hS k) (sortedTimes S hS (k+1)) := by
  have ht := sortedTimes_monotone S hS
  apply intervalIntegrable_of_Ico_eq (ht (Nat.le_succ k))
    (planeSumCost_intervalIntegrable (maskedArray A a b (sortedTimes S hS k)) hh u 0 r
      (ht0.trans_le (ht (Nat.zero_le k))) (ht (Nat.le_succ k)))
  intro s hs
  unfold maskedCost
  rw [maskedArray_const A a b S hS ha hb k hs]

lemma masked_cost_integral_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) (r : Three) :
    strictConstant*(∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      maskedConstant*arrayCubic A h := by
  let t := sortedTimes S hS
  have ht : Monotone t := sortedTimes_monotone S hS
  have ht0 : h^2 ≤ t 0 := hl _ (sortedTimes_mem S hS 0)
  let B : ℕ → Matrix D D ℂ := fun k i j => windowMask (a i j) (b i j) (t k) (A 0 i j)
  have hB (k : ℕ) (i j : D) : ‖B k i j‖ ≤ ‖A 0 i j‖ := windowMask_norm_le _ _ _ _
  have hv (i j : D) : (∑ k ∈ Finset.range (S.card-1), ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖ :=
    sum_windowMask_variation t ht _ _ (hab i j) _ _
  have hin := finite_masked_dissipation D A B hB (S.card-1) hv hh t ht ht0 r
  have he (k : ℕ) : (∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
      (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) =
      ∫ s in t k..t (k+1), maskedCost A a b h (fun m => h*(m:ℤ)) r s := by
    apply intervalIntegral.integral_congr_Ioo_of_le (ht (Nat.le_succ k))
    intro s hs
    unfold maskedCost
    rw [maskedArray_const A a b S hS ha hb k ⟨hs.1.le,hs.2⟩]
    rfl
  simp_rw [he] at hin
  rw [intervalIntegral.sum_integral_adjacent_intervals] at hin
  · simpa only [t,sortedTimes_zero,sortedTimes_last] using hin
  · intro k _
    exact maskedCost_interval_piece A a b S hS ha hb hh _ ((sq_pos_of_pos hh).trans_le ht0) r k
end
end TriangularHilbert.Heat
end

end OAI
