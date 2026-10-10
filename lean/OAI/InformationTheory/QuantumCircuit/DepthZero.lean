import OAI.InformationTheory.QuantumCircuit.Count

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma rankOne_sandwich (v w : Bit → ℂ) :
    rankOne v * rankOne w * rankOne v =
      Complex.normSq (star w ⬝ᵥ v) • rankOne v := by
  ext i j
  simp only [rankOne, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    Complex.real_smul, ← Complex.mul_conj, dotProduct, Pi.star_apply,
    Fin.sum_univ_two, map_add, map_mul, Complex.conj_conj, Complex.star_def]
  ring

open scoped MatrixOrder in
lemma rankOne_markov_le (v w : Bit → ℂ)
    (hv : ∑ b, Complex.normSq (v b) = 1)
    (hw : ∑ b, Complex.normSq (w b) = 1) :
    rankOne v * rankOne w * ((2:ℝ) • (1 - rankOne v) + rankOne v) * rankOne w * rankOne v ≤ 1 := by
  let P := rankOne v
  let Q := rankOne w
  let c : ℝ := Complex.normSq (star w ⬝ᵥ v)
  have hP := rankOne_projection hv
  have hQ := rankOne_projection hw
  have hPQ : P * Q * P = c • P := rankOne_sandwich v w
  have hid : P * Q * ((2:ℝ) • (1 - P) + P) * Q * P = (2*c-c^2) • P := by
    have h1 : P * Q * Q * P = c • P := by rw [mul_assoc P Q Q, hQ.isIdempotentElem.eq, hPQ]
    have h2 : P * Q * P * Q * P = c^2 • P := by
      rw [hPQ, smul_mul_assoc, smul_mul_assoc, hPQ, smul_smul, pow_two]
    calc
      _ = (2:ℝ) • (P * Q * Q * P) - P * Q * P * Q * P := by
        simp only [two_smul, mul_add, add_mul, mul_sub, sub_mul, mul_one]
        abel
      _ = _ := by rw [h1, h2, smul_smul, ← sub_smul]
  change P * Q * ((2:ℝ) • (1 - P) + P) * Q * P ≤ 1
  rw [hid]
  apply sub_nonneg.mp
  have heq : 1 - (2*c-c^2) • P = (1-P) + (1-c)^2 • P := by
    have hc : (1-c)^2 = 1-(2*c-c^2) := by ring
    simp only [hc, sub_smul, one_smul]
    abel
  rw [heq]
  exact add_nonneg hP.one_sub.nonneg (smul_nonneg (sq_nonneg _) hP.nonneg)

lemma tensorMatrix_pattern_scale {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (z : ℝ) :
    tensorMatrix (fun i => if i ∈ M.support then
      (if i ∈ F then z • (1 - rankOne (M.vector i)) else rankOne (M.vector i)) else 1) =
      z ^ F.card • M.pattern F := by
  classical
  have heq : (fun i => if i ∈ M.support then
      (if i ∈ F then z • (1 - rankOne (M.vector i)) else rankOne (M.vector i)) else 1) =
      (fun i => (if i ∈ F then z else 1) •
        (if i ∈ M.support then (if i ∈ F then 1 - rankOne (M.vector i) else rankOne (M.vector i)) else 1)) := by
    funext i
    by_cases hiF : i ∈ F
    · simp [hiF, hF hiF]
    · simp [hiF]
  rw [heq, tensorMatrix_smul]
  congr 1
  simp

/-- The generating function of the mismatch spectral partition. -/
lemma Count.spectral_power_tensor {N : ℕ} (M : Count N) (z : ℝ) :
    (∑ F ∈ M.support.powerset, z ^ F.card • M.pattern F) =
      tensorMatrix (fun i => if i ∈ M.support then
        z • (1 - rankOne (M.vector i)) + rankOne (M.vector i) else 1) := by
  classical
  rw [← tensorMatrix_sum_patterns M.support]
  apply Finset.sum_congr rfl
  intro F hF
  exact (tensorMatrix_pattern_scale M F (Finset.mem_powerset.mp hF) z).symm

open scoped MatrixOrder in
lemma Count.high_le_generating {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r ≤ (2 : ℝ) ^ (-r) •
      (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) := by
  classical
  rw [Finset.smul_sum]
  unfold Count.high
  apply Finset.sum_le_sum
  intro F _
  rw [smul_smul]
  by_cases hr : r ≤ F.card
  · rw [ite_eq_left hr]
    nth_rw 1 [← one_smul ℝ (M.pattern F)]
    apply smul_le_smul_of_nonneg_right _ (M.pattern_projection F).nonneg
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    exact Real.one_le_rpow (by norm_num) (by linarith)
  · rw [ite_eq_right hr]
    exact smul_nonneg (by positivity) (M.pattern_projection F).nonneg


/-- Single-site factor of a product projection. -/
def Count.site {N : ℕ} (M : Count N) (i : Fin N) : QubitOperator :=
  if i ∈ M.support then rankOne (M.vector i) else 1

lemma Count.site_projection {N : ℕ} (M : Count N) (i : Fin N) : IsStarProjection (M.site i) := by
  classical
  dsimp [Count.site]
  split_ifs with hi
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

open scoped MatrixOrder in
lemma projection_markov_nonneg {A : Type*} [Ring A] [StarRing A] [PartialOrder A]
    [StarOrderedRing A] [Algebra ℝ A] [IsOrderedModule ℝ A]
    (P Q : A) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    0 ≤ P * Q * ((2:ℝ) • (1-P)+P) * Q * P := by
  have hn : 0 ≤ (2:ℝ) • (1-P)+P :=
    add_nonneg (smul_nonneg (by norm_num) hP.one_sub.nonneg) hP.nonneg
  simpa only [star_mul, hQ.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq, mul_assoc] using
    star_right_conjugate_nonneg hn (P*Q)

lemma projection_markov_self {A : Type*} [Ring A] [Module ℝ A] [SMulCommClass ℝ A A]
    {P : A} (hP : IsIdempotentElem P) : P * ((2:ℝ) • (1-P)+P) * P = P := by
  have hc : P * (1-P) = 0 := by rw [mul_sub,mul_one,hP.eq,sub_self]
  simp only [mul_add, mul_smul_comm, hc, smul_zero, zero_add, hP.eq]

open scoped MatrixOrder in
lemma Count.markov_site_le {N : ℕ} (M D : Count N) (i : Fin N) :
    M.site i * D.site i * ((2:ℝ) • (1-M.site i)+M.site i) * D.site i * M.site i ≤ 1 := by
  classical
  by_cases hM : i ∈ M.support
  · by_cases hD : i ∈ D.support
    · simp only [Count.site, ite_eq_left hM, ite_eq_left hD]
      exact rankOne_markov_le _ _ (M.normalized i hM) (D.normalized i hD)
    · simp only [Count.site, ite_eq_left hM, ite_eq_right hD, mul_one]
      rw [projection_markov_self (rankOne_projection (M.normalized i hM)).isIdempotentElem]
      exact (rankOne_projection (M.normalized i hM)).le_one
  · have heq : M.site i = 1 := ite_eq_right hM
    rw [heq]
    simp only [sub_self, smul_zero, zero_add, one_mul, mul_one,
      (D.site_projection i).isIdempotentElem.eq]
    exact (D.site_projection i).le_one

lemma Count.generating_eq_sites {N : ℕ} (M : Count N) :
    (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) =
      tensorMatrix (fun i => (2:ℝ) • (1-M.site i)+M.site i) := by
  classical
  rw [M.spectral_power_tensor]
  congr 1
  funext i
  by_cases hi : i ∈ M.support <;> simp [Count.site,hi]

open scoped MatrixOrder in
lemma Count.markov_sandwich_le {N : ℕ} (M D : Count N) :
    M.zero * D.zero * (∑ F ∈ M.support.powerset, (2 : ℝ)^F.card • M.pattern F) *
      D.zero * M.zero ≤ 1 := by
  rw [M.generating_eq_sites]
  change tensorMatrix M.site * tensorMatrix D.site *
    tensorMatrix (fun i => (2:ℝ) • (1-M.site i)+M.site i) *
    tensorMatrix D.site * tensorMatrix M.site ≤ 1
  simp only [tensorMatrix_mul]
  exact tensorMatrix_le_one _
    (fun i => projection_markov_nonneg _ _ (M.site_projection i) (D.site_projection i))
    (fun i => M.markov_site_le D i)

open scoped MatrixOrder in
lemma Count.depth_zero_square {N : ℕ} (M D : Count N) (r : ℝ) :
    ‖M.high r * D.zero * M.zero‖^2 ≤ (2 : ℝ)^(-r) := by
  let A := M.high r * D.zero * M.zero
  have heq : star A * A = M.zero * D.zero * M.high r * D.zero * M.zero := by
    dsimp [A]
    simp only [star_mul, M.zero_projection.isSelfAdjoint.star_eq,
      D.zero_projection.isSelfAdjoint.star_eq, (M.high_projection r).isSelfAdjoint.star_eq]
    simp only [mul_assoc]
    rw [← mul_assoc (M.high r) (M.high r), (M.high_projection r).isIdempotentElem.eq]
  have h := star_right_conjugate_le_conjugate (M.high_le_generating r) (M.zero * D.zero)
  simp only [star_mul, M.zero_projection.isSelfAdjoint.star_eq,
    D.zero_projection.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc] at h
  have hbound : star A * A ≤ (2 : ℝ)^(-r) • (1 : Operator N) := by
    rw [heq]
    exact le_trans (by simpa only [mul_assoc] using h)
      (smul_le_smul_of_nonneg_left (M.markov_sandwich_le D) (by positivity))
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap (star A * A) (by positivity : 0 ≤ (2:ℝ)^(-r)) (star_mul_self_nonneg A)).2
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hbound)
  simpa only [CStarRing.norm_star_mul_self, pow_two] using hn


lemma Count.depth_zero_bound {N : ℕ} (M D : Count N) (r : ℝ) :
    ‖M.high r * D.zero * M.zero‖ ≤ Real.exp (-(Real.log 2 / 2) * r) := by
  have hsq := M.depth_zero_square D r
  have heq : Real.exp (-(Real.log 2 / 2) * r)^2 = (2:ℝ)^(-r) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  rw [← heq] at hsq
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq

end QAC

end

end OAI
