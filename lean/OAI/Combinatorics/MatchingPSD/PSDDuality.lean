import Mathlib
import OAI.Combinatorics.MatchingPSD.OrthogonalCone
import OAI.Combinatorics.MatchingPSD.DeterminantNormalization

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

omit [Fintype I] in
lemma evaluationCone_convex (B : I → Matrix R R ℝ) : Convex ℝ (evaluationCone B) :=
  PerfectMatchingPSD.convex_posSemidef.linear_image (evaluation B)

omit [Fintype I] in
lemma evaluationCone_zero (B : I → Matrix R R ℝ) : 0 ∈ evaluationCone B :=
  ⟨0, Matrix.PosSemidef.zero, map_zero _⟩

omit [Fintype I] in
lemma evaluationCone_smul (B : I → Matrix R R ℝ) {y : I → ℝ}
    (hy : y ∈ evaluationCone B) {t : ℝ} (ht : 0 ≤ t) :
    t • y ∈ evaluationCone B := by
  obtain ⟨A, hA, rfl⟩ := hy
  exact ⟨t • A, hA.smul ht, map_smul _ _ _⟩

lemma trace_evaluation_duality (B : I → Matrix R R ℝ) (c : I → ℝ)
    (A : Matrix R R ℝ) :
    (A * ∑ i, c i • B i).trace = ∑ i, c i * evaluation B A i := by
  simp [evaluation, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_smul]

omit [Fintype I] [DecidableEq R] in
lemma psd_of_trace_nonneg {D : Matrix R R ℝ} (hD : D.IsHermitian)
    (h : ∀ A : Matrix R R ℝ, A.PosSemidef → 0 ≤ (A * D).trace) : D.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hD
  intro x
  have hx : (Matrix.vecMulVec x x).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star x
  have ht := h _ hx
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm] at ht
  simpa only [star_trivial] using ht

lemma exists_psd_evaluation (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (y : I → ℝ)
    (hy : ∀ c : I → ℝ, (∑ i, c i • B i).PosSemidef → 0 ≤ ∑ i, c i * y i) :
    ∃ A : Matrix R R ℝ, A.PosSemidef ∧ evaluation B A = y := by
  classical
  change y ∈ evaluationCone B
  by_contra hn
  obtain ⟨f, u, hfy, hu⟩ := geometric_hahn_banach_point_closed
    (evaluationCone_convex B) (evaluationCone_isClosed B hB) hn
  have hu0 : u < 0 := by simpa using hu 0 (evaluationCone_zero B)
  have hfn (z : I → ℝ) (hz : z ∈ evaluationCone B) : 0 ≤ f z := by
    by_contra hneg
    have hnz : f z < 0 := lt_of_not_ge hneg
    have hratio : 0 < u / f z := div_pos_of_neg_of_neg hu0 hnz
    have ht := hu ((u / f z + 1) • z)
      (evaluationCone_smul B hz (by linarith : 0 ≤ u / f z + 1))
    rw [map_smul, smul_eq_mul] at ht
    have he : (u / f z + 1) * f z = u + f z := by
      field_simp [ne_of_lt hnz]
    rw [he] at ht
    linarith
  let c : I → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hf (z : I → ℝ) : f z = ∑ i, c i * z i := by
    simpa only [ContinuousLinearMap.coe_coe, c, smul_eq_mul, mul_comm] using f.toLinearMap.pi_apply_eq_sum_univ z
  have hD : (∑ i, c i • B i).PosSemidef := by
    apply psd_of_trace_nonneg
    · exact isSelfAdjoint_sum univ (fun i _ => (hB i).isHermitian.smul (by simp [IsSelfAdjoint]))
    · intro A hA
      rw [trace_evaluation_duality, ← hf]
      exact hfn _ ⟨A, hA, rfl⟩
  have h := hy c hD
  rw [← hf] at h
  linarith

end AffinePSD

end OAI
