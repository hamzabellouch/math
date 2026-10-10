import OAI.Analysis.OInfinity.RohlinGluing

namespace OAI

/-! # Both unitary defects of a weighted Rohlin sum

The diagonal coefficient/projection commutators control both defects. The
second estimate compares the adjoint weighted sum with the weighted adjoints;
it does not require pairwise commutation of all coefficients and projections.
The hypotheses still have to be supplied by the actual tower construction.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

lemma adjoint_unitary_commutator_norm (u : unitary E) (e : E)
    (he : star e = e) :
    ‖(star u : unitary E) * e - e * (star u : unitary E)‖ =
      ‖(u : E) * e - e * (u : E)‖ := by
  calc
    _ = ‖star ((star u : unitary E) * e - e * (star u : unitary E))‖ :=
      (norm_star _).symm
    _ = ‖e * (u : E) - (u : E) * e‖ := by
      simp only [star_sub, star_mul, he, Unitary.coe_star, star_star]
    _ = _ := norm_sub_rev _ _

lemma star_mul_self_sub_norm_le (x y : E) :
    ‖star x * x - star y * y‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have hid : star x * x - star y * y =
      star x * (x - y) + star (x - y) * y := by
    rw [star_sub]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖star x * (x - y)‖ + ‖star (x - y) * y‖ := norm_add_le _ _
    _ ≤ ‖x‖ * ‖x - y‖ + ‖x - y‖ * ‖y‖ := by
      simpa only [norm_star] using add_le_add
        (norm_mul_le (star x) (x - y)) (norm_mul_le (star (x - y)) y)
    _ = _ := by ring

lemma finiteRohlinSum_norm_le [Nontrivial E] (v : I → unitary E) (e : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) :
    ‖finiteRohlinSum v e‖ ≤ Real.sqrt (Fintype.card I) := by
  change ‖∑ i, (v i : E) * e i‖ ≤ _
  simpa only [mul_one] using orthogonalWeighted_norm_le e (fun i => (v i : E))
    he hee horth 1 (by norm_num) (fun i => (CStarRing.norm_coe_unitary (v i)).le)

omit [DecidableEq I] in
lemma finiteRohlinSum_star_commutator_le (v : I → unitary E) (e : I → E)
    (he : ∀ i, star (e i) = e i) (δ : ℝ)
    (hc : ∀ i, ‖(v i : E) * e i - e i * (v i : E)‖ ≤ δ) :
    ‖star (finiteRohlinSum v e) - finiteRohlinSum (fun i => star (v i)) e‖ ≤
      (Fintype.card I : ℝ) * δ := by
  change ‖star (∑ i, (v i : E) * e i) - ∑ i, (star (v i) : unitary E) * e i‖ ≤ _
  rw [star_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖star ((v i : E) * e i) - (star (v i) : unitary E) * e i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ : I, δ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [star_mul, he i, Unitary.coe_star, norm_sub_rev]
      exact (adjoint_unitary_commutator_norm (v i) (e i) (he i)).le.trans (hc i)
    _ = _ := by simp

/-- The second defect has a dimension-dependent bound, sufficient when the
commutator accuracy is chosen after the finite tower size. -/
lemma finiteRohlinSum_isometry_defect_le [Nontrivial E] (v : I → unitary E) (e : I → E)
    (he : ∀ i, star (e i) = e i) (hee : ∀ i, e i * e i = e i)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : (∑ i, e i) = 1) (δ : ℝ)
    (hc : ∀ i, ‖(v i : E) * e i - e i * (v i : E)‖ ≤ δ) :
    ‖star (finiteRohlinSum v e) * finiteRohlinSum v e - 1‖ ≤
      (Fintype.card I : ℝ) * (2 * Real.sqrt (Fintype.card I) + 1) * δ := by
  let z := finiteRohlinSum v e
  let y := finiteRohlinSum (fun i => star (v i)) e
  have hz : ‖z‖ ≤ Real.sqrt (Fintype.card I) := finiteRohlinSum_norm_le v e he hee horth
  have hy : ‖y‖ ≤ Real.sqrt (Fintype.card I) :=
    finiteRohlinSum_norm_le (fun i => star (v i)) e he hee horth
  have hc' (i : I) : ‖(star (v i) : unitary E) * e i -
      e i * (star (v i) : unitary E)‖ ≤ δ :=
    (adjoint_unitary_commutator_norm (v i) (e i) (he i)).le.trans (hc i)
  have hydef : ‖y * star y - 1‖ ≤ (Fintype.card I : ℝ) * δ :=
    finiteRohlinSum_coisometry_defect_le (fun i => star (v i)) e he hee horth hsum δ hc'
  have hdist : ‖z - star y‖ ≤ (Fintype.card I : ℝ) * δ := by
    calc
      _ = ‖star z - y‖ := by rw [← norm_star (star z - y), star_sub, star_star]
      _ ≤ _ := finiteRohlinSum_star_commutator_le v e he δ hc
  have hdiff : ‖star z * z - y * star y‖ ≤
      (2 * Real.sqrt (Fintype.card I)) * ((Fintype.card I : ℝ) * δ) := by
    calc
      _ = ‖star z * z - star (star y) * star y‖ := by rw [star_star]
      _ ≤ (‖z‖ + ‖star y‖) * ‖z - star y‖ := star_mul_self_sub_norm_le z (star y)
      _ ≤ (2 * Real.sqrt (Fintype.card I)) * ((Fintype.card I : ℝ) * δ) := by
        rw [norm_star]
        exact mul_le_mul (by linarith) hdist (norm_nonneg _)
          (by positivity)
  change ‖star z * z - 1‖ ≤ _
  calc
    _ ≤ ‖star z * z - y * star y‖ + ‖y * star y - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 * Real.sqrt (Fintype.card I)) * ((Fintype.card I : ℝ) * δ) +
        (Fintype.card I : ℝ) * δ := add_le_add hdiff hydef
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
