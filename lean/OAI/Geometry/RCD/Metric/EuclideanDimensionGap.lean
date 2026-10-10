import OAI.Geometry.RCD.Harmonic.MeanGramControl
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace OAI

/-!
# The finite-dimensional obstruction to an extra Euclidean factor

A map from R^(n+1) to R^n cannot have an almost identity Gram operator.
This supplies the algebraic part of the quantitative non-(n+1)-splitting
condition in the published harmonic transformation theorem.
-/

open scoped InnerProductSpace BigOperators

noncomputable section

namespace RegularPointCoordinates

/-- Injectivity forced by a Gram error strictly below one contradicts dimension. -/
theorem extra_dimension_gram_gap (n : ℕ)
    (F : Euclidean (n + 1) →L[ℝ] Euclidean n) :
    1 ≤ ‖F.adjoint.comp F - ContinuousLinearMap.id ℝ (Euclidean (n + 1))‖ := by
  by_contra hnot
  have hsmall := lt_of_not_ge hnot
  have hinj : Function.Injective F := by
    apply (injective_iff_map_eq_zero F.toLinearMap).mpr
    intro v hv
    change F v = 0 at hv
    have hlow := inner_lower_of_sub_id_norm (F.adjoint.comp F) le_rfl v
    have hzero : ⟪v, (F.adjoint.comp F) v⟫_ℝ = 0 := by
      change ⟪v, F.adjoint (F v)⟫_ℝ = 0
      rw [hv, map_zero, inner_zero_right]
    rw [hzero] at hlow
    have hvnorm : ‖v‖ = 0 := by
      apply le_antisymm _ (norm_nonneg v)
      by_contra h
      exact (not_lt_of_ge hlow) (mul_pos (sub_pos.mpr hsmall) (sq_pos_of_pos (lt_of_not_ge h)))
    exact norm_eq_zero.mp hvnorm
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := F.toLinearMap) hinj
  simp only [finrank_euclideanSpace_fin] at hdim
  omega

/-- The continuous linear map with the specified Euclidean columns. -/
def euclideanColumnMap {k n : ℕ} (v : Fin k → Euclidean n) :
    Euclidean k →L[ℝ] Euclidean n := ∑ i, (EuclideanSpace.proj i).smulRight (v i)

@[simp] theorem euclideanColumnMap_single {k n : ℕ} (v : Fin k → Euclidean n) (i : Fin k) :
    euclideanColumnMap v (EuclideanSpace.single i 1) = v i := by
  classical
  simp [euclideanColumnMap, PiLp.single_apply]

/-- An explicit upper bound on entrywise almost-orthonormality is impossible
for n+1 vectors in R^n. -/
theorem extra_dimension_inner_error (n : ℕ) (v : Fin (n + 1) → Euclidean n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgram : ∀ i j, |⟪v i, v j⟫_ℝ - (if i = j then 1 else 0)| ≤ ε) :
    1 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * ε := by
  let F := euclideanColumnMap v
  refine (extra_dimension_gram_gap n F).trans ?_
  apply euclidean_operator_norm_le_of_entries _ hε
  intro i j
  have he : ((F.adjoint.comp F) (EuclideanSpace.single j 1)) i = ⟪v j, v i⟫_ℝ := by
    have hh : ⟪(F.adjoint.comp F) (EuclideanSpace.single j 1), EuclideanSpace.single i 1⟫_ℝ =
        ⟪v j, v i⟫_ℝ := by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      simp only [F, euclideanColumnMap_single]
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using hh
  simpa only [sub_apply, ContinuousLinearMap.id_apply, PiLp.sub_apply,
    PiLp.single_apply, he, eq_comm] using hgram j i

/-- Squared distances of the vertices of an orthogonal simplex cannot all
be too accurate in one dimension less. -/
theorem extra_dimension_squared_distance_error (n : ℕ) (p : Euclidean n)
    (x : Fin (n + 1) → Euclidean n) {ε : ℝ} (hε : 0 ≤ ε)
    (hbase : ∀ i, |dist (x i) p ^ 2 - 1| ≤ ε)
    (hpair : ∀ i j, i ≠ j → |dist (x i) (x j) ^ 2 - 2| ≤ ε) :
    1 ≤ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 * ε := by
  let v := fun i => x i - p
  have hlen (i) : |‖v i‖ ^ 2 - 1| ≤ ε := by
    simpa only [v, dist_eq_norm] using hbase i
  have hd (i j) (hij : i ≠ j) : |‖v i - v j‖ ^ 2 - 2| ≤ ε := by
    have he : v i - v j = x i - x j := by dsimp only [v]; module
    simpa only [he, dist_eq_norm] using hpair i j hij
  have hg : ∀ i j, |⟪v i, v j⟫_ℝ - (if i = j then 1 else 0)| ≤ 2 * ε := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa only [ite_true, real_inner_self_eq_norm_sq] using
        (hlen i).trans (by linarith)
    · rw [ite_eq_right hij, sub_zero]
      have hi := abs_le.mp (hlen i)
      have hj := abs_le.mp (hlen j)
      have hdist := abs_le.mp (hd i j hij)
      have hsq := norm_sub_sq_real (v i) (v j)
      apply abs_le.mpr
      constructor <;> nlinarith
  have hb := extra_dimension_inner_error n v (by positivity : 0 ≤ 2 * ε) hg
  nlinarith

private theorem sq_error_le_five {d a η : ℝ} (hd : 0 ≤ d) (ha : 0 ≤ a) (ha2 : a ≤ 2)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (herr : |d - a| ≤ η) : |d ^ 2 - a ^ 2| ≤ 5 * η := by
  have hupper : d + a ≤ 5 := by have h := (abs_le.mp herr).2; linarith
  calc
    |d ^ 2 - a ^ 2| = |d - a| * (d + a) := by
      rw [← abs_of_nonneg (add_nonneg hd ha), ← abs_mul]
      congr 1
      ring
    _ ≤ η * (d + a) := mul_le_mul_of_nonneg_right herr (add_nonneg hd ha)
    _ ≤ 5 * η := by nlinarith

/-- A metric formulation suited to composing Gromov--Hausdorff approximations. -/
theorem extra_dimension_distance_error (n : ℕ) (p : Euclidean n)
    (x : Fin (n + 1) → Euclidean n) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hbase : ∀ i, |dist (x i) p - 1| ≤ η)
    (hpair : ∀ i j, i ≠ j → |dist (x i) (x j) - Real.sqrt 2| ≤ η) :
    1 ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * η := by
  have hb : ∀ i, |dist (x i) p ^ 2 - 1| ≤ 5 * η := by
    intro i
    simpa only [one_pow] using sq_error_le_five dist_nonneg (by norm_num) (by norm_num)
      hη hη1 (hbase i)
  have hp : ∀ i j, i ≠ j → |dist (x i) (x j) ^ 2 - 2| ≤ 5 * η := by
    intro i j hij
    have hs : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using
      sq_error_le_five dist_nonneg (Real.sqrt_nonneg 2) hs hη hη1 (hpair i j hij)
  have h := extra_dimension_squared_distance_error n p x (by positivity) hb hp
  nlinarith

/-- The same obstruction at an arbitrary positive length scale. -/
theorem extra_dimension_scaled_distance_error (n : ℕ) (p : Euclidean n)
    (x : Fin (n + 1) → Euclidean n) {a ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε)
    (hbase : ∀ i, |dist (x i) p - a| ≤ ε)
    (hpair : ∀ i j, i ≠ j → |dist (x i) (x j) - Real.sqrt 2 * a| ≤ ε) :
    a ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 * ε := by
  have hfactor : 1 ≤ 10 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  by_cases hea : a ≤ ε
  · exact hea.trans (by nlinarith)
  have hnonneg : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hdist (v w : Euclidean n) : dist (a⁻¹ • v) (a⁻¹ • w) = a⁻¹ * dist v w := by
    rw [dist_smul₀, Real.norm_of_nonneg hnonneg]
  have hb (i) : |dist (a⁻¹ • x i) (a⁻¹ • p) - 1| ≤ ε / a := by
    rw [hdist]
    have he : a⁻¹ * dist (x i) p - 1 = a⁻¹ * (dist (x i) p - a) := by field_simp
    rw [he, abs_mul, abs_of_nonneg hnonneg, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hbase i) hnonneg).trans_eq (mul_comm _ _)
  have hp (i j) (hij : i ≠ j) :
      |dist (a⁻¹ • x i) (a⁻¹ • x j) - Real.sqrt 2| ≤ ε / a := by
    rw [hdist]
    have he : a⁻¹ * dist (x i) (x j) - Real.sqrt 2 =
        a⁻¹ * (dist (x i) (x j) - Real.sqrt 2 * a) := by field_simp
    rw [he, abs_mul, abs_of_nonneg hnonneg, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left (hpair i j hij) hnonneg).trans_eq (mul_comm _ _)
  have h := extra_dimension_distance_error n (a⁻¹ • p) (fun i => a⁻¹ • x i)
    (div_nonneg hε ha.le) ((div_le_one ha).mpr (le_of_not_ge hea)) hb hp
  have := (mul_le_mul_of_nonneg_right h ha.le)
  field_simp at this
  nlinarith

end RegularPointCoordinates

end

end OAI
