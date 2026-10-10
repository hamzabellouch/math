import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_adjugate_entry (i j : ι) :
    ContDiff ℝ ∞ (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) := by
  simp only [Matrix.adjugate_apply]
  change ContDiff ℝ ∞ (continuousDetRows ∘ fun A : ι → ι → ℝ =>
    fun l m => Matrix.updateRow (Matrix.of A) j (Pi.single i 1) l m)
  apply (continuousDetRows (ι := ι)).contDiff.comp
  apply contDiff_pi.mpr
  intro l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne hl, Matrix.of_apply]
    fun_prop

lemma contDiffAt_inverse_matrix_entry {A : ℝ → Matrix ι ι ℝ} {t : ℝ}
    (hA : ContDiffAt ℝ ∞ (fun r i j => A r i j) t) (hd : (A t).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ ∞ (fun r => (A r)⁻¹ i j) t := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (((continuousDetRows (ι := ι)).contDiff.contDiffAt.comp t hA).inv hd).mul
    ((contDiff_adjugate_entry i j).contDiffAt.comp t hA)

lemma hasDerivAt_det_entries {A : ℝ → Matrix ι ι ℝ} {D : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun r => A r i j) (D i j) t) :
    HasDerivAt (fun r => (A r).det)
      (∑ i, ∑ j, (A t).adjugate j i * D i j) t := by
  have hd : HasDerivAt (fun r i j => A r i j) (fun i j => D i j) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hA i j
  have hh := (continuousDetRows (ι := ι)).hasFDerivAt (fun i j => A t i j)
    |>.comp_hasDerivAt t hd
  simp only [ContinuousMultilinearMap.linearDeriv_apply] at hh
  convert! hh using 1
  symm
  apply Finset.sum_congr rfl
  intro i _
  change ((A t).updateRow i (D i)).det = _
  rw [det_updateRow_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.adjugate_apply, mul_comm]

/- The conormal for the genuine variation (x+t a(x),u(x)+t beta(x)),
written in its first jets, is (-q(t),1). -/
def variationConormal (D : Matrix ι ι ℝ) (g d : ι → ℝ) (t : ℝ) (k : ι) : ℝ :=
  ∑ l, (g l + t * d l) * (1 + t • D)⁻¹ l k

/- The second form for that conormal. H,B are the Hessians of u,beta;
C k is the Hessian of the kth horizontal displacement. -/
def variationSecondForm (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  H + t • B - t • (Matrix.of fun i j => ∑ k, variationConormal D g d t k * C k i j)

def variationAreaDensity (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) (δ : ℝ) (t : ℝ) : ℝ :=
  Real.rpow (variationSecondForm H B D g d C t).det δ *
    Real.rpow |(1 + t • D).det| ((Fintype.card ι : ℝ) * δ)

@[simp] lemma variationConormal_zero (D : Matrix ι ι ℝ) (g d : ι → ℝ) (k : ι) :
    variationConormal D g d 0 k = g k := by
  simp [variationConormal, Matrix.one_apply]

@[simp] lemma variationSecondForm_zero (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) : variationSecondForm H B D g d C 0 = H := by
  simp [variationSecondForm]

lemma contDiffAt_variationConormal (D : Matrix ι ι ℝ) (g d : ι → ℝ) (k : ι) :
    ContDiffAt ℝ ∞ (fun t => variationConormal D g d t k) 0 := by
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul (by fun_prop)
  apply contDiffAt_inverse_matrix_entry
  · apply contDiffAt_pi.mpr; intro i
    apply contDiffAt_pi.mpr; intro j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  · simp

lemma hasDerivAt_variationSecondForm (H B D : Matrix ι ι ℝ) (g d : ι → ℝ)
    (C : ι → Matrix ι ι ℝ) (i j : ι) :
    HasDerivAt (fun t => variationSecondForm H B D g d C t i j)
      (B i j - ∑ k, g k * C k i j) 0 := by
  have hc : DifferentiableAt ℝ (fun t => ∑ k, variationConormal D g d t k * C k i j) 0 := by
    apply DifferentiableAt.fun_sum
    intro k _
    exact ((contDiffAt_variationConormal D g d k).differentiableAt (by simp)).mul_const _
  have hh := (((hasDerivAt_id (0 : ℝ)).mul_const (B i j)).const_add (H i j)).sub
    ((hasDerivAt_id (0 : ℝ)).mul hc.hasDerivAt)
  convert! hh using 1
  simp

lemma hasDerivAt_variationAreaDensity_raw (H B D : Matrix ι ι ℝ) (hH : H.PosDef)
    (g d : ι → ℝ) (C : ι → Matrix ι ι ℝ) (δ : ℝ) :
    HasDerivAt (variationAreaDensity H B D g d C δ)
      (δ * Real.rpow H.det (δ - 1) *
        (∑ i, ∑ j, H.adjugate j i * (B i j - ∑ k, g k * C k i j)) +
        Real.rpow H.det δ * ((Fintype.card ι : ℝ) * δ * D.trace)) 0 := by
  have hh := (hasDerivAt_det_entries (hasDerivAt_variationSecondForm H B D g d C)).rpow_const
    (p := δ) (Or.inl (by simpa using ne_of_gt hH.det_pos))
  simp only [variationSecondForm_zero] at hh
  have hj : HasDerivAt (fun t : ℝ => (1 + t • D).det) D.trace 0 := by
    simpa [Matrix.adjugate_one, Matrix.one_apply, Matrix.trace] using
      (hasDerivAt_det_line (1 : Matrix ι ι ℝ) D)
  have haj := (hasDerivAt_abs_pos (by simp : 0 < (1 + (0 : ℝ) • D).det)).comp 0 hj
  have hp := haj.rpow_const (p := (Fintype.card ι : ℝ) * δ) (Or.inl (by simp))
  have hhj := hh.mul hp
  convert! hhj using 1
  simp [variationSecondForm_zero, mul_assoc, mul_comm, mul_left_comm]

end AffineBernstein
end

end OAI
