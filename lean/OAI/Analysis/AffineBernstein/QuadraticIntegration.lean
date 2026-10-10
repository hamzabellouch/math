import Mathlib

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The last, purely analytic step of the rescaling argument: a C³ function
with zero third derivative everywhere is exactly its quadratic Taylor polynomial. -/
theorem quadratic_of_third_fderiv_zero (f : E → ℝ) (hf : ContDiff ℝ 3 f)
    (hthird : ∀ x, fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x = 0) :
    ∀ x, f x = (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ f) 0 x x) +
      fderiv ℝ f 0 x + f 0 := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  let L := fderiv ℝ f 0
  have hf₂ : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hf₁ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) :=
    hf₂.fderiv_right (by norm_num)
  have hB (x : E) : fderiv ℝ (fderiv ℝ f) x = B :=
    is_const_of_fderiv_eq_zero (hf₁.differentiable (by norm_num)) hthird x 0
  have hL (x : E) : fderiv ℝ f x = B x + L := by
    have hd (y : E) : HasFDerivAt (fun z => fderiv ℝ f z - B z)
        (0 : E →L[ℝ] E →L[ℝ] ℝ) y := by
      convert (((hf₂.differentiable (by norm_num)) y).hasFDerivAt.sub
        (B.hasFDerivAt (x := y))) using 1
      rw [hB, sub_self]
    have heq := is_const_of_fderiv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).fderiv) x 0
    simp only [map_zero, sub_zero] at heq
    simpa only [add_comm] using sub_eq_iff_eq_add.mp heq
  have hsym (x y : E) : B x y = B y x := by
    exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)) x y
  let q : E → ℝ := fun x => (1 / 2 : ℝ) * (B x x) + L x + f 0
  have hq (x : E) : HasFDerivAt q (B x + L) x := by
    have hBi : HasFDerivAt (fun y => B y y) (B x + B.flip x) x := by
      convert B.hasFDerivAt.clm_apply (hasFDerivAt_id (𝕜 := ℝ) x) using 1 <;>
        rfl
    have hBx : B.flip x = B x := by
      ext y
      exact hsym y x
    have hhalf : (1 / 2 : ℝ) • (B x + B.flip x) = B x := by
      rw [hBx, ← two_smul ℝ (B x), smul_smul]
      norm_num
    convert ((hBi.const_mul (1 / 2 : ℝ)).add (L.hasFDerivAt (x := x))).add_const (f 0)
      using 1
    simp only [hhalf]
  have hd (x : E) : HasFDerivAt (fun y => f y - q y) (0 : E →L[ℝ] ℝ) x := by
    convert (((hf.differentiable (by norm_num)) x).hasFDerivAt.sub (hq x)) using 1
    rw [hL, sub_self]
  intro x
  have hconst := is_const_of_fderiv_eq_zero (fun y => (hd y).differentiableAt)
    (fun y => (hd y).fderiv) x 0
  simp only [q, map_zero, mul_zero, zero_add, sub_self] at hconst
  exact sub_eq_zero.mp hconst

end AffineBernstein

end

end OAI
