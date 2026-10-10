import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.EmpiricalTensor

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Density
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma psd_trace_domination {B : Matrix I I ℂ} (hB : B.PosSemidef) :
    (B.trace • (1 : Matrix I I ℂ) - B).PosSemidef := by
  let U : unitaryGroup I ℂ := hB.1.eigenvectorUnitary
  let e : I → ℝ := hB.1.eigenvalues
  have he (i) : 0 ≤ e i := hB.eigenvalues_nonneg i
  have htr : B.trace = ∑ j, (e j : ℂ) := hB.1.trace_eq_sum_eigenvalues
  have hs : B = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (e i : ℂ)) *
      star (U : Matrix I I ℂ) := hB.1.spectral_theorem
  let d : I → ℂ := fun i => B.trace - (e i : ℂ)
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    have hh := Finset.single_le_sum (fun j _ => he j) (Finset.mem_univ i)
    have hc : (e i : ℂ) ≤ ∑ j, (e j : ℂ) := by exact_mod_cast hh
    dsimp only [d]
    rw [htr]
    exact sub_nonneg.mpr hc
  have hp := (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same (U : Matrix I I ℂ)
  have hdiag : Matrix.diagonal d = B.trace • (1 : Matrix I I ℂ) -
      Matrix.diagonal (fun i => (e i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, d]
  have hmain : (U : Matrix I I ℂ) * Matrix.diagonal d * star (U : Matrix I I ℂ) =
      B.trace • 1 - B := by
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, ← Unitary.coe_star, Unitary.coe_mul_star_self, Unitary.coe_star, ← hs]
  exact hmain ▸ hp

omit [DecidableEq I] in
lemma rankOne_conjugate {J : Type*} [Fintype J] [DecidableEq J] (P : Matrix J I ℂ) (v : I → ℂ) :
    P * rankOne v * P.conjTranspose = rankOne (P.mulVec v) := by
  simp only [rankOne, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose,
    star_star]

lemma rankOne_projection_bound (P : Matrix I I ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (v : I → ℂ) (hv : P.mulVec v = v) :
    ((rankOne v).trace • P - rankOne v).PosSemidef := by
  have hh := (psd_trace_domination (rankOne_psd v)).mul_mul_conjTranspose_same P
  have he : P * ((rankOne v).trace • (1 : Matrix I I ℂ) - rankOne v) * P.conjTranspose =
      (rankOne v).trace • P - rankOne v := by
    rw [Matrix.mul_sub, Matrix.sub_mul, rankOne_conjugate, hv,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hP.eq, hPP]
  exact he ▸ hh

variable {A : Type*} [Fintype A] [DecidableEq A]

lemma symmetricProjector_identity (n : ℕ) (x : (Fin n → A) → ℂ)
    (hx : ∀ w v, wordCounts w = wordCounts v → x w = x v) :
    (symmetricProjector n).mulVec x = x := by
  funext w
  change (∑ v, (if wordType n w = wordType n v then
    ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0) * x v) = x w
  have he (v) : (if wordType n w = wordType n v then
      ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) else 0) * x v =
      if wordType n v = wordType n w then
        ((Nat.multinomial Finset.univ (wordType n w).val : ℝ)⁻¹ : ℂ) * x w else 0 := by
    by_cases h : wordType n w = wordType n v
    · rw [ite_eq_left h, ite_eq_left h.symm, hx w v ((wordType_eq_iff n w v).mp h)]
    · simp [h, Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (Finset.univ.filter (fun v : Fin n → A => wordType n v = wordType n w)).card =
      Nat.multinomial Finset.univ (wordType n w).val := by
    rw [← Fintype.card_subtype, card_wordType]
  rw [hc]
  have hn : (Nat.multinomial Finset.univ (wordType n w).val : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (wordType n w).val))
  push_cast
  field_simp

lemma symmetricProjector_idempotent (n : ℕ) :
    symmetricProjector (A := A) n * symmetricProjector n = symmetricProjector n := by
  ext w v
  have h := symmetricProjector_identity n (fun u => symmetricProjector n u v) (by
    intro u t hut
    simp only [symmetricProjector, wordType_eq_iff, hut]
    have ht : wordType n u = wordType n t := (wordType_eq_iff n u t).mpr hut
    rw [ht])
  exact congrFun h w

lemma symmetric_rankOne_bound (n : ℕ) (v : (Fin n → A) → ℂ)
    (hv : ∀ w u, wordCounts w = wordCounts u → v w = v u) :
    ((rankOne v).trace • symmetricProjector n - rankOne v).PosSemidef :=
  rankOne_projection_bound _ (symmetricProjector_psd n).1
    (symmetricProjector_idempotent n) _ (symmetricProjector_identity n v hv)

theorem symmetric_vector_postselection (n : ℕ) (hn : 0 < n) (v : (Fin n → A) → ℂ)
    (hv : ∀ w u, wordCounts w = wordCounts u → v w = v u) :
    (((rankOne v).trace * ((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - rankOne v).PosSemidef := by
  have hh := (finite_postselection (A := A) n hn).smul (rankOne_psd v).trace_nonneg
  have hr := symmetric_rankOne_bound n v hv
  have he : ((rankOne v).trace * ((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - rankOne v =
      (rankOne v).trace • ((((n+1 : ℕ) : ℂ)^Fintype.card A) •
      (∑ c : WordType A n, phaseAverage n (empirical n c)) - symmetricProjector n) +
      ((rankOne v).trace • symmetricProjector n - rankOne v) := by
    simp only [smul_sub, smul_smul]
    abel
  rw [he]
  exact hh.add hr

end BinaryCoordinateSweeps.Density

end

end OAI
