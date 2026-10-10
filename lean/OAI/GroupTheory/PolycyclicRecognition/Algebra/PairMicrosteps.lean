import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConvexMicrosteps
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeanControl

namespace OAI

/-! # Exact normalized pair-height microsteps

The inverse power in the normalized left action records the original right
translation of the sampling point. The final group remainder is retained.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set
open scoped BigOperators NNReal

variable {G W : Type*} [Group G] [MetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}

omit [NormedSpace ℝ W] in
/-- The actual height cocycle telescopes along successive right microsteps. -/
theorem pairHeight_pow_sum (π : G →* Multiplicative W) (g : G)
    (p : NormalizedPair G Λ) (n : ℕ) :
    pairHeight π (g ^ n) p =
      ∑ j ∈ Finset.range n, pairHeight π g ((g ^ j)⁻¹ • p) := by
  induction n with
  | zero => simp [pairHeight, p.property.2]
  | succ n ih =>
    rw [pow_succ, pairHeight_cocycle, ih, Finset.sum_range_succ]

omit [NormedSpace ℝ W] in
/-- Keep the final incomplete step in the telescoping identity. -/
theorem pairHeight_pow_mul (π : G →* Multiplicative W) (g h : G)
    (p : NormalizedPair G Λ) (n : ℕ) :
    pairHeight π (g ^ n * h) p =
      (∑ j : Fin n, pairHeight π g ((g ^ (j : ℕ))⁻¹ • p)) +
        pairHeight π h ((g ^ n)⁻¹ • p) := by
  rw [pairHeight_cocycle, pairHeight_pow_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => pairHeight π g ((g ^ j)⁻¹ • p)) n).symm

/-- The convex distance estimate for the exact microstep decomposition, before
bounding the final incomplete step by the Lipschitz constant. -/
theorem normalized_pair_microsteps_convex_bound
    (π : G →* Multiplicative W) (g h : G) (p : NormalizedPair G Λ)
    (n : ℕ) {L t : ℝ} (hL : 0 < L) (ht : 0 < t) (hn : (n : ℝ) * L ≤ t)
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S) :
    infDist (t⁻¹ • pairHeight π (g ^ n * h) p) (convexHull ℝ S) ≤
      (L / t) * (∑ j : Fin n,
        infDist (L⁻¹ • pairHeight π g ((g ^ (j : ℕ))⁻¹ • p)) S) +
      ‖t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p) - (1 - (n : ℝ) * (L / t)) • w₀‖ := by
  have ha : (∑ _j : Fin n, L / t) ≤ 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc]
    exact (div_le_one ht).mpr hn
  have h := infDist_weighted_sum_le hS hw₀ (fun _ : Fin n => L / t)
    (fun _ => (div_pos hL ht).le) ha
    (fun j => L⁻¹ • pairHeight π g ((g ^ (j : ℕ))⁻¹ • p))
    (t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p))
  have hscale : (L / t) * L⁻¹ = t⁻¹ := by field_simp
  simpa only [smul_smul, hscale, ← Finset.smul_sum, ← smul_add,
    ← pairHeight_pow_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] using h

/-- Lipschitz height control makes the incomplete microstep cost at most its
relative length times one fixed constant. -/
theorem normalized_pair_microsteps_convex_bound_of_remainder
    (π : G →* Multiplicative W) (hπ : LipschitzWith K (fun g => (π g).toAdd))
    (g h : G) (p : NormalizedPair G Λ) (n : ℕ)
    {L t D : ℝ} (hL : 0 < L) (ht : 0 < t) (_hD : 0 ≤ D)
    (hn : (n : ℝ) * L ≤ t) (hn' : t ≤ ((n : ℝ) + 1) * L)
    (hrem : dist 1 h ≤ D * L)
    {S : Set W} (hS : IsCompact S) {w₀ : W} (hw₀ : w₀ ∈ S) :
    infDist (t⁻¹ • pairHeight π (g ^ n * h) p) (convexHull ℝ S) ≤
      (L / t) * (∑ j : Fin n,
        infDist (L⁻¹ • pairHeight π g ((g ^ (j : ℕ))⁻¹ • p)) S) +
      (L / t) * ((K : ℝ) * Λ * D + ‖w₀‖) := by
  have heq : 1 - (n : ℝ) * (L / t) = (t - (n : ℝ) * L) / t := by
    field_simp
  have hpos : 0 ≤ 1 - (n : ℝ) * (L / t) := by
    rw [heq]
    exact div_nonneg (sub_nonneg.mpr hn) ht.le
  have hsmall : 1 - (n : ℝ) * (L / t) ≤ L / t := by
    rw [heq]
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith
  have hnorm : ‖t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p)‖ ≤
      (L / t) * ((K : ℝ) * Λ * D) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    calc
      _ ≤ t⁻¹ * ((K : ℝ) * Λ * dist 1 h) :=
        mul_le_mul_of_nonneg_left (norm_pairHeight_le π hπ h _) (inv_nonneg.mpr ht.le)
      _ ≤ t⁻¹ * ((K : ℝ) * Λ * (D * L)) := by gcongr
      _ = _ := by ring
  apply (normalized_pair_microsteps_convex_bound π g h p n hL ht hn hS hw₀).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ‖t⁻¹ • pairHeight π h ((g ^ n)⁻¹ • p)‖ +
        ‖(1 - (n : ℝ) * (L / t)) • w₀‖ := norm_sub_le _ _
    _ ≤ (L / t) * ((K : ℝ) * Λ * D) + (L / t) * ‖w₀‖ := by
      have hw : ‖(1 - (n : ℝ) * (L / t)) • w₀‖ ≤ (L / t) * ‖w₀‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
        exact mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      exact add_le_add hnorm hw
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
