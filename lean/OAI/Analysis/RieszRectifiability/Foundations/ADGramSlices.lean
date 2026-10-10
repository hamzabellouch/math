import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.DyadicLipschitzFamily

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem DyadicLipschitzFamily.fine_slice_bound {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (i : ι) (t : Finset ι) (k : ℕ)
    (hlevel : ∀ j ∈ t, F.level j = F.level i + k)
    (hnonzero : ∀ j ∈ t, (∫ x, F.test i x * F.test j x ∂μ) ≠ 0) :
    ∑ j ∈ t, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      ((G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        F.weight i * (1 / 2 : ℝ) ^ k := by
  have hlev (j : ι) (hj : j ∈ t) : F.level i ≤ F.level j := by rw [hlevel j hj]; omega
  have hmass := finite_AD_fine_interaction_mass n C G hC μ hg hlower t F.center F.radius c J hc hJ
    (fun j _ => F.center_mem j) (fun j _ => F.radius_pos j) (fun j _ => F.core_admissible j)
    (F.center i) (F.radius i) (F.radius_pos i) (fun j hj => F.radius_antitone i j (hlev j hj))
    (fun j hj => by
      have h := nonzero_gram_centers_near μ (F.test i) (F.test j) (F.center i) (F.center j)
        (J * F.radius i) (J * F.radius j) (F.support_ball i) (F.support_ball j) (hnonzero j hj)
      simpa only [dist_comm] using! h.le)
    (fun j hj l hl hne => F.separated j l (by rw [hlevel j hj, hlevel l hl]) hne)
  have hratio (j : ι) (hj : j ∈ t) : F.radius j / F.radius i = (1 / 2 : ℝ) ^ k := by
    rw [F.scale_eq i j (hlev j hj), hlevel j hj, Nat.add_sub_cancel_left]
    field_simp [(F.radius_pos i).ne']
  let P := G * J ^ (n + 1) * A ^ 2
  have hP : 0 ≤ P := by dsimp [P]; have hG := hg.1; positivity
  calc
    _ ≤ ∑ j ∈ t, P * (1 / 2 : ℝ) ^ k * (F.weight j ^ 2 / F.weight i) := by
      apply Finset.sum_le_sum
      intro j hj
      have h := F.fine_gram G hg hJ hA i j
      rw [hratio j hj] at h
      exact h
    _ = (P * (1 / 2 : ℝ) ^ k / F.weight i) * ∑ j ∈ t, F.radius j ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [F.weight_sq j]
      ring
    _ ≤ (P * (1 / 2 : ℝ) ^ k / F.weight i) *
        (interactionPackingConstant n C G c J * F.radius i ^ n) :=
      mul_le_mul_of_nonneg_left hmass (by have hwi := F.weight_pos i; positivity)
    _ = _ := by
      rw [← F.weight_sq i]
      dsimp only [P]
      field_simp [(F.weight_pos i).ne']

theorem DyadicLipschitzFamily.coarse_slice_bound {ι : Type*} {n d : ℕ}
    {μ : Measure (Ambient d)} {c J A : ℝ} (F : DyadicLipschitzFamily ι n d μ c J A)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 ≤ A) (i : ι) (t : Finset ι) (k : ℕ)
    (hlevel : ∀ j ∈ t, F.level j + k = F.level i)
    (hnonzero : ∀ j ∈ t, (∫ x, F.test i x * F.test j x ∂μ) ≠ 0) :
    ∑ j ∈ t, |∫ x, F.test i x * F.test j x ∂μ| * F.weight j ≤
      ((G * J ^ (n + 1) * A ^ 2) * interactionPackingConstant n C G c J) *
        F.weight i * (1 / 2 : ℝ) ^ k := by
  classical
  have hP : 0 ≤ G * J ^ (n + 1) * A ^ 2 := by have hG := hg.1; positivity
  have hB : 0 ≤ interactionPackingConstant n C G c J := by
    dsimp [interactionPackingConstant]
    have hG := hg.1
    positivity
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp only [Finset.sum_empty]
    have hwi := F.weight_pos i
    positivity
  obtain ⟨j₀, hj₀⟩ := ht
  have hlev (j : ι) (hj : j ∈ t) : F.level j ≤ F.level i := by have h := hlevel j hj; omega
  have heq (j : ι) (hj : j ∈ t) : F.radius j = F.radius j₀ :=
    F.radius_eq_of_level_eq j j₀ (by have h1 := hlevel j hj; have h2 := hlevel j₀ hj₀; omega)
  have hnear : ∀ j ∈ t, dist (F.center j) (F.center i) ≤ J * F.radius i + J * F.radius j₀ := by
    intro j hj
    have h := nonzero_gram_centers_near μ (F.test i) (F.test j) (F.center i) (F.center j)
      (J * F.radius i) (J * F.radius j) (F.support_ball i) (F.support_ball j) (hnonzero j hj)
    rw [heq j hj] at h
    simpa only [dist_comm] using! h.le
  have hcard := finite_AD_coarse_interaction_card n C G hC μ hg hlower t F.center (F.radius j₀)
    c J (F.radius_pos j₀) hc hJ (fun j _ => F.center_mem j) (F.core_admissible j₀)
    (F.center i) (F.radius i) (F.radius_antitone j₀ i (hlev j₀ hj₀)) hnear (by
      intro j hj l hl hne
      have h := F.separated j l (by have h1 := hlevel j hj; have h2 := hlevel l hl; omega) hne
      simpa only [heq j hj, heq l hl] using! h)
  have hratio (j : ι) (hj : j ∈ t) : F.radius i / F.radius j = (1 / 2 : ℝ) ^ k := by
    have hsub : F.level i - F.level j = k := by have h := hlevel j hj; omega
    rw [F.scale_eq j i (hlev j hj), hsub]
    field_simp [(F.radius_pos j).ne']
  calc
    _ ≤ ∑ _j ∈ t, (G * J ^ (n + 1) * A ^ 2) * (1 / 2 : ℝ) ^ k * F.weight i := by
      apply Finset.sum_le_sum
      intro j hj
      have h := F.coarse_gram G hg hJ hA i j
      rw [hratio j hj] at h
      exact h
    _ = (t.card : ℝ) * ((G * J ^ (n + 1) * A ^ 2) * (1 / 2 : ℝ) ^ k * F.weight i) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ interactionPackingConstant n C G c J *
        ((G * J ^ (n + 1) * A ^ 2) * (1 / 2 : ℝ) ^ k * F.weight i) :=
      mul_le_mul_of_nonneg_right hcard (by have hwi := F.weight_pos i; positivity)
    _ = _ := by ring

end

end RieszRectifiability

end OAI
