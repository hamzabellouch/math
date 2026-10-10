import OAI.Analysis.OInfinity.RohlinGluing
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

namespace OAI

/-! # Dimension-independent estimates for finite tower bands

A fixed band has orthogonal initial and final projection corners. Its norm
is therefore bounded by its largest coefficient, independently of the number
of tower cells. This is the estimate used for adjacent path samples.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

omit [Fintype I] in
private lemma orthogonalSelfAdjoint_sum_bound (f : I → E)
    (hf : ∀ i, IsSelfAdjoint (f i))
    (ho : ∀ i j, i ≠ j → f i * f j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i, ‖f i‖ ≤ M) (s : Finset I) :
    ‖∑ i ∈ s, f i‖ ≤ M := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, norm_zero] using hM
  | @insert j s hj ih =>
      have hs : IsSelfAdjoint (∑ i ∈ s, f i) := by
        change star (∑ i ∈ s, f i) = _
        rw [star_sum]
        exact Finset.sum_congr rfl fun i _ => (hf i).star_eq
      have hp : f j * (∑ i ∈ s, f i) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact ho j i (by intro h; subst i; exact hj hi)
      rw [Finset.sum_insert hj, (hf j).norm_add_eq_max hs hp]
      exact max_le (hb j) ih

/-- A family with pairwise orthogonal initial and final supports has the
supremum norm estimate; in particular no cardinality factor is needed. -/
lemma orthogonalSupported_sum_norm_le (b : I → E)
    (hl : ∀ i j, i ≠ j → star (b i) * b j = 0)
    (hr : ∀ i j, i ≠ j → b i * star (b j) = 0)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i, ‖b i‖ ≤ M) :
    ‖∑ i, b i‖ ≤ M := by
  have heq : star (∑ i, b i) * (∑ i, b i) = ∑ i, star (b i) * b i := by
    rw [star_sum, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_eq_single i
      (fun j _ hji => hl i j hji.symm) (by simp)
  have hc (i : I) : ‖star (b i) * b i‖ ≤ M ^ 2 := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg (b i), hb i]
  have horth (i j : I) (hij : i ≠ j) :
      (star (b i) * b i) * (star (b j) * b j) = 0 := by
    calc
      _ = star (b i) * (b i * star (b j)) * b j := by noncomm_ring
      _ = 0 := by rw [hr i j hij, mul_zero, zero_mul]
  have h := orthogonalSelfAdjoint_sum_bound (fun i => star (b i) * b i)
    (fun i => IsSelfAdjoint.star_mul_self (b i)) horth (M ^ 2) (sq_nonneg M) hc Finset.univ
  rw [← heq, CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (∑ i, b i)]

/-- One finite matrix band, indexed by its domain cells. -/
def towerBand (e : I → E) (σ : Equiv.Perm I) (x : I → E) : E :=
  ∑ i, e (σ i) * x i * e i

lemma towerBand_norm_le (e : I → E) (σ : Equiv.Perm I) (x : I → E)
    (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hx : ∀ i, ‖x i‖ ≤ M) :
    ‖towerBand e σ x‖ ≤ M := by
  apply orthogonalSupported_sum_norm_le (fun i => e (σ i) * x i * e i) ?_ ?_ M hM ?_
  · intro i j hij
    rw [star_mul, star_mul, (he i).isSelfAdjoint.star_eq,
      (he (σ i)).isSelfAdjoint.star_eq]
    calc
      _ = e i * star (x i) * (e (σ i) * e (σ j)) * x j * e j := by noncomm_ring
      _ = 0 := by rw [ho (σ i) (σ j) (σ.injective.ne hij)]; simp
  · intro i j hij
    rw [star_mul, star_mul, (he j).isSelfAdjoint.star_eq,
      (he (σ j)).isSelfAdjoint.star_eq]
    calc
      _ = e (σ i) * x i * (e i * e j) * star (x j) * e (σ j) := by noncomm_ring
      _ = 0 := by rw [ho i j hij]; simp
  · intro i
    calc
      _ ≤ ‖e (σ i)‖ * ‖x i‖ * ‖e i‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1 * M * 1 := by
        gcongr
        · exact (he (σ i)).norm_le
        · exact hx i
        · exact (he i).norm_le
      _ = M := by ring

/-- Changing every coefficient by at most ε changes a fixed band by at
most ε, independently of the number of cells. -/
lemma towerBand_sub_norm_le (e : I → E) (σ : Equiv.Perm I) (x y : I → E)
    (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (hxy : ∀ i, ‖x i - y i‖ ≤ ε) :
    ‖towerBand e σ x - towerBand e σ y‖ ≤ ε := by
  have h : towerBand e σ x - towerBand e σ y = towerBand e σ (fun i => x i - y i) := by
    simp only [towerBand, ← Finset.sum_sub_distrib, mul_sub, sub_mul]
  rw [h]
  exact towerBand_norm_le e σ _ he ho ε hε hxy

end WeakPureInfiniteness

end

end OAI
