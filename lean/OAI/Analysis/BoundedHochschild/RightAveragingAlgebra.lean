import OAI.Analysis.BoundedHochschild.CompletelyBoundedRows

namespace OAI

/-!
# Composition and convex combinations of elementary right averages

Normalized finite coefficient families are closed under concatenation and
products. Thus the elementary averages form the convex semigroup used in the
module-map projection argument.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]
variable {I J : Type*} [Fintype I] [Fintype J]

lemma finiteRightAverage_reindex (e : I ≃ J) (m : J → M) (T : M →L[ℂ] M) :
    finiteRightAverage (m ∘ e) T = finiteRightAverage m T := by
  ext a
  simpa only [finiteRightAverage_apply, Function.comp_apply] using
    e.sum_comp (fun j => T (a * m j) * star (m j))

lemma rightAverage_product_normalized (m : I → M) (n : J → M)
    (hm : ∑ i, m i * star (m i) = 1) (hn : ∑ j, n j * star (n j) = 1) :
    ∑ p : I × J, (m p.1 * n p.2) * star (m p.1 * n p.2) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, m i * (∑ j, n j * star (n j)) * star (m i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
    _ = 1 := by simp only [hn, mul_one, hm]

lemma finiteRightAverage_comp (m : I → M) (n : J → M) (T : M →L[ℂ] M) :
    finiteRightAverage m (finiteRightAverage n T) =
      finiteRightAverage (fun p : I × J => m p.1 * n p.2) T := by
  classical
  ext a
  simp only [finiteRightAverage_apply, Fintype.sum_prod_type, Finset.sum_mul,
    star_mul, mul_assoc]

lemma finiteRightAverage_sum (m : I → M) (n : J → M) (T : M →L[ℂ] M) :
    finiteRightAverage (Sum.elim m n) T = finiteRightAverage m T + finiteRightAverage n T := by
  ext a
  simp only [finiteRightAverage_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, add_apply]

lemma finiteRightAverage_real_smul (m : I → M) (r : ℝ) (T : M →L[ℂ] M) :
    finiteRightAverage (fun i => r • m i) T = (r * r) • finiteRightAverage m T := by
  ext a
  have hT (b : M) : T (r • b) = r • T b := (T.restrictScalars ℝ).map_smul r b
  simp only [finiteRightAverage_apply, mul_smul_comm, hT,
    star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← Finset.smul_sum, smul_apply]

lemma rightAverage_real_smul_normalized (m : I → M) (r : ℝ)
    (hm : ∑ i, m i * star (m i) = 1) :
    ∑ i, (r • m i) * star (r • m i) = (r * r) • (1 : M) := by
  simp only [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← Finset.smul_sum, hm]

/-- Joining square-root-scaled coefficient families realizes a convex
combination without changing normalization. -/
lemma rightAverage_convex_normalized (m : I → M) (n : J → M)
    (hm : ∑ i, m i * star (m i) = 1) (hn : ∑ j, n j * star (n j) = 1)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1) :
    ∑ p : I ⊕ J,
      (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j) p) *
        star (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j) p) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [rightAverage_real_smul_normalized m _ hm, rightAverage_real_smul_normalized n _ hn,
    Real.mul_self_sqrt hr, Real.mul_self_sqrt hs, ← add_smul, hrs, one_smul]

lemma finiteRightAverage_convex (m : I → M) (n : J → M)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (T : M →L[ℂ] M) :
    finiteRightAverage
      (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j)) T =
        r • finiteRightAverage m T + s • finiteRightAverage n T := by
  rw [finiteRightAverage_sum, finiteRightAverage_real_smul,
    finiteRightAverage_real_smul, Real.mul_self_sqrt hr, Real.mul_self_sqrt hs]

end BoundedHochschild.KadisonRingrose

end

end OAI
