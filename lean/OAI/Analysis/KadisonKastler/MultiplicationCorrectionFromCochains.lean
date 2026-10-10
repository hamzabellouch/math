import OAI.Analysis.KadisonKastler.MultiplicationCorrectionSequence
import OAI.Analysis.KadisonKastler.CompleteCorrectionProducts

namespace OAI

/-! # From the quadratic cochain estimate to multiplication correction

The analytic cochain selector is kept as an explicit argument. The product
iteration and its complete bound are proved here, not postulated.
-/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem multiplication_correction_of_quadratic_cochains
    (hsolver : QuadraticCochainSolver A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hms : ∀ x y, star (m x y) = m (star y) (star x))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/11)
    (hb : HaagerupBound (m - LinearMap.mul ℂ A) q) :
    ∃ T : A ≃ₗ[ℂ] A, (∀ x y, T (m x y) = T x * T y) ∧
      (∀ x, T (star x) = star (T x)) ∧
      CompletelyBoundedBy (T.toLinearMap - LinearMap.id) (4 * q) := by
  let initial : SmallAssociativeProduct A q := ⟨m, hm, hms, hb⟩
  obtain ⟨P, hP0, U, hUs, hUb, hnext⟩ :=
    exists_halving_multiplication_sequence hsolver hq hq1 initial
  have hUbound (n : ℕ) : CompletelyBoundedBy (U n).toLinearMap
      (1 + correctionScale q n) := by
    have he : (U n).toLinearMap = LinearMap.id + ((U n).toLinearMap - LinearMap.id) := by abel
    rw [he]
    exact (completelyBoundedBy_id (A := A)).add (hUb n)
  let S (n : ℕ) : A →L[ℂ] A := (hUbound n).toContinuousLinearMap
  have hSU (n : ℕ) (x : A) : S n x = U n x := rfl
  have hScb (n : ℕ) : CompletelyBoundedBy ((S n).toLinearMap - LinearMap.id)
      (correctionScale q n) := hUb n
  have hsmall (n : ℕ) : 2 * ∑ i ∈ Finset.range n, correctionScale q i ≤ 1 := by
    have h := correctionScale_partial_sum hq n
    linarith
  have hLb (n : ℕ) := correctionProducts_complete_bounds S (correctionScale q)
    (correctionScale_nonneg hq) hsmall hScb n
  have hintertwine (n : ℕ) (x y : A) :
      correctionProducts S n (m x y) =
        (P n).mul (correctionProducts S n x) (correctionProducts S n y) := by
    induction n with
    | zero =>
      change m x y = (P 0).mul x y
      exact congrArg (fun f : A →ₗ[ℂ] A →ₗ[ℂ] A => f x y) hP0.symm
    | succ n ih =>
      simp only [correctionProducts_succ, ContinuousLinearMap.comp_apply, ih, hnext,
        conjugatedBilinear_apply, hSU, (U n).symm_apply_apply]
  have herror (n : ℕ) (x y : A) :
      ‖correctionProducts S n (m x y) -
          correctionProducts S n x * correctionProducts S n y‖ ≤
        (4 * correctionScale q n) * ‖x‖ * ‖y‖ := by
    rw [hintertwine]
    have h := (P n).bound.apply_norm_le (correctionProducts S n x) (correctionProducts S n y)
    change ‖(P n).mul (correctionProducts S n x) (correctionProducts S n y) -
      correctionProducts S n x * correctionProducts S n y‖ ≤ _ at h
    calc
      _ ≤ correctionScale q n * ‖correctionProducts S n x‖ * ‖correctionProducts S n y‖ := h
      _ ≤ correctionScale q n * (2 * ‖x‖) * (2 * ‖y‖) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left ((hLb n).2.apply_norm_le x) (correctionScale_nonneg hq n)
        · exact (hLb n).2.apply_norm_le y
        · exact norm_nonneg _
        · exact mul_nonneg (correctionScale_nonneg hq n) (mul_nonneg (by norm_num) (norm_nonneg x))
      _ = _ := by ring
  have hcsum : Summable (fun n => 2 * correctionScale q n) :=
    (correctionScale_summable q).mul_left 2
  have hctotal : (∑' n, 2 * correctionScale q n) = 4 * q := by
    rw [tsum_mul_left, correctionScale_tsum]
    ring
  have hcsmall : (∑' n, 2 * correctionScale q n) < 1 := by
    rw [hctotal]
    linarith
  have hLstep (n : ℕ) : CompletelyBoundedBy
      ((correctionProducts S (n+1)).toLinearMap - (correctionProducts S n).toLinearMap)
      (2 * correctionScale q n) := by
    rw [correctionProducts_increment]
    convert (hScb n).comp (hLb n).2 (correctionScale_nonneg hq n) using 1
    ring
  obtain ⟨T, hTm, hTs, hTc⟩ := correction_of_summable_steps m (correctionProducts S)
    (correctionProducts_zero S) (fun n => 2 * correctionScale q n)
    (fun n => 4 * correctionScale q n)
    (fun n => mul_nonneg (by norm_num) (correctionScale_nonneg hq n)) hcsum hcsmall hLstep
    (correctionProducts_star S (fun n x => by simpa only [hSU] using hUs n x))
    (by simpa only [mul_zero] using (correctionScale_tendsto q).const_mul 4) herror
  exact ⟨T, hTm, hTs, by simpa only [hctotal] using hTc⟩

end

end KadisonKastler

end OAI
