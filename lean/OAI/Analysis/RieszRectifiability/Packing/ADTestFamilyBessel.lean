import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.ADGramSlices

namespace OAI

/-!
# Bessel estimate for dyadic Lipschitz test families

Summable bounds on the scale slices of the Gram matrix give a Bessel inequality
for finite families of test functions under upper growth and lower AD bounds.
The resulting constant depends explicitly on the interaction packing estimate.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicLipschitzFamily.bessel {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (s : Finset ι)
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) :
    ∑ i ∈ s, (∫ x, F.test i x * u x ∂μ) ^ 2 ≤
      (4 * (G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, u x ^ 2 ∂μ := by
  classical
  let : IsFiniteMeasureOnCompacts μ := globalGrowth_finite_on_compacts G μ hg
  let P := G * J ^ (n + 1) * A ^ 2
  let B := interactionPackingConstant n C G c J
  have hP : 0 ≤ P := by dsimp [P]; have hG := hg.1; positivity
  have hB : 0 ≤ B := by dsimp [B, interactionPackingConstant]; have hG := hg.1; positivity
  have hslice : ∀ i ∈ s, ∀ k : ℕ,
      ∑ j ∈ s with Nat.dist (F.level i) (F.level j) = k,
        |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
        (2 * P * B) * F.weight i * (1 / 2 : ℝ) ^ k := by
    intro i _ k
    let q := s.filter (fun j => Nat.dist (F.level i) (F.level j) = k)
    let t := q.filter (fun j => (∫ x, F.test i x * F.test j x ∂μ) ≠ 0)
    have hdrop : (∑ j ∈ q, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j) =
        ∑ j ∈ t, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hnot
      have hz : (∫ x, F.test i x * F.test j x ∂μ) = 0 := by
        by_contra hn
        exact hnot (Finset.mem_filter.mpr ⟨hj, hn⟩)
      simp only [hz, abs_zero, zero_mul]
    have hnonzero (j : ι) (hj : j ∈ t) : (∫ x, F.test i x * F.test j x ∂μ) ≠ 0 :=
      (Finset.mem_filter.mp hj).2
    have hgap (j : ι) (hj : j ∈ t) : Nat.dist (F.level i) (F.level j) = k :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    have hf := F.fine_slice_bound C G hC hg hlower hc hJ hA i
      (t.filter (fun j => F.level i ≤ F.level j)) k (by
        intro j hj
        obtain ⟨hjt, hle⟩ := Finset.mem_filter.mp hj
        have h := hgap j hjt
        rw [Nat.dist_eq_sub_of_le hle] at h
        omega) (fun j hj => hnonzero j (Finset.mem_filter.mp hj).1)
    have hco := F.coarse_slice_bound C G hC hg hlower hc hJ hA i
      (t.filter (fun j => ¬ F.level i ≤ F.level j)) k (by
        intro j hj
        obtain ⟨hjt, hlt⟩ := Finset.mem_filter.mp hj
        have h := hgap j hjt
        rw [Nat.dist_eq_sub_of_le_right (by omega)] at h
        omega) (fun j hj => hnonzero j (Finset.mem_filter.mp hj).1)
    change (∑ j ∈ q, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j) ≤ _
    rw [hdrop, ← Finset.sum_filter_add_sum_filter_not t (fun j => F.level i ≤ F.level j)]
    have h := add_le_add hf hco
    convert! h using 1
    dsimp only [P, B]
    ring
  have hb := finite_L2_bessel_of_geometric_gram_slices μ s F.test (fun i => (F.memLp_integrable i).1)
    F.weight (fun i j => Nat.dist (F.level i) (F.level j)) (2 * P * B) (by positivity)
    (fun i _ => F.weight_pos i) hslice u hu
  convert! hb using 1
  dsimp only [P, B]
  ring

theorem DyadicLipschitzFamily.packing_of_large_pairings {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (s : Finset ι)
    (u : Ambient d → ℝ) (hu : MemLp u 2 μ) (v : ℝ) (hv : 0 < v)
    (hlarge : ∀ i ∈ s, v ^ 2 * F.radius i ^ n ≤ (∫ x, F.test i x * u x ∂μ) ^ 2) :
    ∑ i ∈ s, F.radius i ^ n ≤
      ((4 * (G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        ∫ x, u x ^ 2 ∂μ) / v ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
  calc
    _ = ∑ i ∈ s, v ^ 2 * F.radius i ^ n := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ s, (∫ x, F.test i x * u x ∂μ) ^ 2 := Finset.sum_le_sum hlarge
    _ ≤ _ := F.bessel C G hC hg hlower hc hJ hA s u hu

end

end RieszRectifiability

end OAI
