import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.TraceInterpolation

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixMoment (q : ℕ) (A : M ι) : ℝ := (Matrix.trace ((star A * A)^q)).re

lemma diagReal_pow (s : ι → ℝ) (q : ℕ) :
    (diagReal s)^q = diagReal (fun i => s i ^ q) := by
  simp [diagReal, Matrix.diagonal_pow]

lemma trace_unitary_conj (V : Matrix.unitaryGroup ι ℂ) (B : M ι) :
    Matrix.trace ((V : M ι) * B * star (V : M ι)) = Matrix.trace B := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma unitary_conj_pow (V : Matrix.unitaryGroup ι ℂ) (B : M ι) (q : ℕ) :
    ((V : M ι) * B * star (V : M ι))^q = (V : M ι) * B^q * star (V : M ι) := by
  have h := ((Unitary.conjStarAlgAut ℂ (M ι) V).toAlgEquiv.map_pow B q).symm
  change (Unitary.conjStarAlgAut ℂ (M ι) V B)^q =
    Unitary.conjStarAlgAut ℂ (M ι) V (B^q) at h
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star] using h

lemma matrixMoment_of_svd (A : M ι) (q : ℕ) (V : Matrix.unitaryGroup ι ℂ)
    (s : ι → ℝ) (hgram : star A * A = (V : M ι) * diagReal (fun i => s i^2) * star (V : M ι)) :
    matrixMoment q A = ∑ i, s i ^ (2*q) := by
  rw [matrixMoment, hgram, unitary_conj_pow, trace_unitary_conj, diagReal_pow]
  simp only [diagReal, Matrix.trace_diagonal,
    Complex.re_sum, Complex.ofReal_re, ← pow_mul]

lemma matrixMoment_nonneg (q : ℕ) (A : M ι) : 0 ≤ matrixMoment q A := by
  obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  rw [matrixMoment_of_svd A q V s hg]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (hs i) _)

lemma matrixMoment_eq_zero_iff {q : ℕ} (hq : 0 < q) (A : M ι) :
    matrixMoment q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
    rw [matrixMoment_of_svd A q V s hg] at h
    have hi : ∀ i, s i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => pow_nonneg (hs j) (2*q))).mp h
      exact (pow_eq_zero_iff (by omega : 2*q ≠ 0)).mp (hz i (Finset.mem_univ _))
    rw [hA]
    simp [diagReal, hi]
  · intro h
    simp [matrixMoment, h, zero_pow (by omega : q ≠ 0)]

lemma unitary_norm_le_one (V : Matrix.unitaryGroup ι ℂ) : ‖(V : M ι)‖ ≤ 1 := by
  have h1 : ‖(1 : M ι)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  have h : ‖(V : M ι)‖ * ‖(V : M ι)‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Unitary.coe_star_mul_self]
    exact h1
  nlinarith [norm_nonneg (V : M ι)]

omit [Fintype ι] in
lemma diagPower_real (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) {x : ℝ} (hx : 0 < x) :
    diagPower d (x : ℂ) = diagReal (fun i => (d i) ^ x) := by
  unfold diagPower diagReal
  congr 1
  funext i
  by_cases hi : d i = 0
  · simp [hi, Real.zero_rpow hx.ne']
  · rw [ite_eq_right hi]
    change Complex.exp ((x : ℂ) * (Real.log (d i) : ℂ)) = ((d i ^ x : ℝ) : ℂ)
    rw [Real.rpow_def_of_pos (lt_of_le_of_ne (hd i) (Ne.symm hi))]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    ring

lemma density_normalization {m : ℕ} (hm : 0 < m) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    {t : ℝ} (ht : 0 < t) (hts : ∑ i, s i^m = t) :
    let d : ι → ℝ := fun i => s i ^ m / t
    (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
    diagReal s = (t ^ ((m : ℝ)⁻¹) : ℝ) • diagPower d (((m : ℝ)⁻¹ : ℝ) : ℂ) := by
  dsimp only
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : ∀ i, 0 ≤ s i^m/t := fun i => div_nonneg (pow_nonneg (hs i) _) ht.le
  refine ⟨hd, ?_, ?_⟩
  · rw [← Finset.sum_div, hts, div_self ht.ne']
  · rw [diagPower_real _ hd (inv_pos.mpr hm')]
    unfold diagReal
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    change (s i : ℂ) = ((t ^ (m : ℝ)⁻¹ : ℝ) : ℂ) *
      (((s i ^ m / t) ^ (m : ℝ)⁻¹ : ℝ) : ℂ)
    rw [Real.div_rpow (pow_nonneg (hs i) _) ht.le,
      Real.pow_rpow_inv_natCast (hs i) (Nat.ne_of_gt hm)]
    norm_cast
    exact (mul_div_cancel₀ (s i) (Real.rpow_pos_of_pos ht _).ne').symm

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
