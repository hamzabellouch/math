import OAI.Geometry.Arnold.Orbit

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Forms

abbrev CSpace (n : ℕ) := Fin n → ℂ

def reCoord (n : ℕ) (i : Fin n) : CSpace n →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj i)

def imCoord (n : ℕ) (i : Fin n) : CSpace n →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj i)

@[simp] lemma reCoord_apply (n : ℕ) (i : Fin n) (z : CSpace n) : reCoord n i z = (z i).re := rfl
@[simp] lemma imCoord_apply (n : ℕ) (i : Fin n) (z : CSpace n) : imCoord n i z = (z i).im := rfl

/-- Exactly the normalization d(sum x dy-y dx). -/
def symplectic (n : ℕ) : CSpace n →L[ℝ] CSpace n →L[ℝ] ℝ :=
  2 • ∑ i : Fin n, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp (reCoord n i) (imCoord n i) -
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (imCoord n i) (reCoord n i))

lemma symplectic_apply (n : ℕ) (u v : CSpace n) :
    symplectic n u v = 2 * ∑ i, ((u i).re * (v i).im - (u i).im * (v i).re) := by
  simp [symplectic, _root_.sum_apply, ContinuousLinearMap.bilinearComp_apply]

lemma symplectic_skew (n : ℕ) (u v : CSpace n) :
    symplectic n u v = -symplectic n v u := by
  rw [symplectic_apply, symplectic_apply, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma symplectic_eq (n : ℕ) (u v : CSpace n) :
    symplectic n u v = 2 * (∑ i, star (u i) * v i).im := by
  simp [symplectic_apply, Complex.mul_im, sub_eq_add_neg, Finset.sum_add_distrib]

/-- Euclidean squared norm, not the sup norm of the Pi ambient Banach space. -/
def normSq (n : ℕ) (z : CSpace n) : ℝ := ∑ i, Complex.normSq (z i)

lemma normSq_contDiff (n : ℕ) : ContDiff ℝ ∞ (normSq n) := by
  unfold normSq
  apply ContDiff.sum
  intro i _
  simpa only [Complex.normSq_apply, reCoord_apply, imCoord_apply] using
    (((reCoord n i).contDiff.mul (reCoord n i).contDiff).add
      ((imCoord n i).contDiff.mul (imCoord n i).contDiff))

lemma normSq_nonneg (n : ℕ) (z : CSpace n) : 0 ≤ normSq n z :=
  Finset.sum_nonneg (fun _ _ ↦ Complex.normSq_nonneg _)

lemma normSq_eq_zero_iff (n : ℕ) (z : CSpace n) : normSq n z = 0 ↔ z = 0 := by
  constructor
  · intro h
    ext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ Complex.normSq_nonneg (z j))).mp h i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  · rintro rfl
    simp [normSq]

lemma normSq_smul (n : ℕ) (a : ℂ) (z : CSpace n) :
    normSq n (a • z) = Complex.normSq a * normSq n z := by
  simp [normSq, Complex.normSq_mul, Finset.mul_sum]

lemma symplectic_I_left (n : ℕ) (z v : CSpace n) :
    symplectic n (Complex.I • z) v =
      -2 * ∑ i, ((z i).re * (v i).re + (z i).im * (v i).im) := by
  rw [symplectic_apply]
  have h (i : Fin n) :
      ((Complex.I • z) i).re * (v i).im - ((Complex.I • z) i).im * (v i).re =
        -((z i).re * (v i).re + (z i).im * (v i).im) := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

/-- The radial derivative identity making the curvature basic on unit spheres. -/
lemma normSq_fderiv (n : ℕ) (z v : CSpace n) :
    fderiv ℝ (normSq n) z v = -symplectic n (Complex.I • z) v := by
  have hderiv : HasFDerivAt (normSq n)
      (∑ i : Fin n, ((2 * (z i).re) • reCoord n i + (2 * (z i).im) • imCoord n i)) z := by
    convert! HasFDerivAt.sum (u := Finset.univ) (fun i _ ↦
      (((reCoord n i).hasFDerivAt.mul (reCoord n i).hasFDerivAt).add
        ((imCoord n i).hasFDerivAt.mul (imCoord n i).hasFDerivAt))) using 1
    · funext x
      simp [normSq, Complex.normSq_apply]
    · ext w
      simp only [_root_.sum_apply, _root_.add_apply,
        _root_.smul_apply, reCoord_apply, imCoord_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [hderiv.fderiv, symplectic_I_left]
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, reCoord_apply, imCoord_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ArnoldCounterexample.Forms

end

end OAI
