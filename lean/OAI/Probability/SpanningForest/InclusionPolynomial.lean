import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Polynomial Matrix
open Polynomial Finset

namespace Problem336
namespace InclusionPolynomial

variable {E R : Type*} [DecidableEq E] [CommRing R]

theorem coeff_marked_power (T F : Finset E) :
    ((1 + X : R[X]) ^ (T ∩ F).card).coeff F.card = if F ⊆ T then 1 else 0 := by
  rw [Polynomial.coeff_one_add_X_pow]
  by_cases h : F ⊆ T
  · have hI : T ∩ F = F := Finset.inter_eq_right.mpr h
    simp [h, hI]
  · have hlt : (T ∩ F).card < F.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.inter_subset_right, ?_⟩
      intro heq
      apply h
      rw [← heq]
      exact Finset.inter_subset_left
    simp [h, Nat.choose_eq_zero_of_lt hlt]

theorem coeff_partition (trees : Finset (Finset E)) (w : Finset E → R) (F : Finset E) :
    (∑ T ∈ trees, C (w T) * (1 + X : R[X]) ^ (T ∩ F).card).coeff F.card =
      ∑ T ∈ trees with F ⊆ T, w T := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, coeff_marked_power]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

theorem coeff_det_one_add_X_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι R) :
    ((1 + (X : R[X]) • K.map C).det).coeff (Fintype.card ι) = K.det := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp only [← Finset.card_univ (α := ι), Finset.powersetCard_self,
    Finset.sum_singleton]
  exact Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun i : ι => Finset.mem_univ i)) K

theorem inclusion_mass_eq_of_partition_identity
    (trees : Finset (Finset E)) (w : Finset E → R) (F : Finset E)
    (K : Matrix F F R) (Z : R)
    (hpoly : (∑ T ∈ trees, C (w T) * (1 + X : R[X]) ^ (T ∩ F).card) =
      C Z * (1 + (X : R[X]) • K.map C).det) :
    (∑ T ∈ trees with F ⊆ T, w T) = Z * K.det := by
  have hcoeff := congrArg (fun p : R[X] => p.coeff F.card) hpoly
  rw [coeff_partition, Polynomial.coeff_C_mul] at hcoeff
  have htop : ((1 + (X : R[X]) • K.map C).det).coeff F.card = K.det := by
    simpa only [Fintype.card_coe] using coeff_det_one_add_X_top K
  rwa [htop] at hcoeff

theorem inclusion_ratio_eq_of_partition_identity
    (trees : Finset (Finset E)) (w : Finset E → ℝ) (F : Finset E)
    (K : Matrix F F ℝ) (Z : ℝ) (hZ : Z ≠ 0)
    (hpoly : (∑ T ∈ trees, C (w T) * (1 + X : ℝ[X]) ^ (T ∩ F).card) =
      C Z * (1 + (X : ℝ[X]) • K.map C).det) :
    (∑ T ∈ trees with F ⊆ T, w T) / Z = K.det := by
  rw [inclusion_mass_eq_of_partition_identity trees w F K Z hpoly]
  field_simp

theorem eval_zero_partition
    (trees : Finset (Finset E)) (w : Finset E → R) (F : Finset E) :
    (∑ T ∈ trees, C (w T) * (1 + X : R[X]) ^ (T ∩ F).card).eval 0 =
      ∑ T ∈ trees, w T := by
  simp [Polynomial.eval_finsetSum]

theorem eval_det_marker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (t : ℝ) :
    ((1 + (X : ℝ[X]) • K.map C).det).eval t = (1 + t • K).det := by
  change (Polynomial.evalRingHom t) ((1 + (X : ℝ[X]) • K.map C).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem inclusion_ratio_eq_of_real_marker_identity
    (trees : Finset (Finset E)) (w : Finset E → ℝ) (F : Finset E)
    (K : Matrix F F ℝ) (Z : ℝ) (hZ : Z ≠ 0)
    (hmarker : ∀ t : ℝ, (∑ T ∈ trees, w T * (1 + t) ^ (T ∩ F).card) =
      Z * (1 + t • K).det) :
    (∑ T ∈ trees with F ⊆ T, w T) / Z = K.det := by
  apply inclusion_ratio_eq_of_partition_identity trees w F K Z hZ
  apply Polynomial.funext
  intro t
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
    eval_det_marker] using hmarker t

end InclusionPolynomial
end Problem336

end

end OAI
